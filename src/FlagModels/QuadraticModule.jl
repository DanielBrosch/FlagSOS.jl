export QuadraticModule

"""
    QuadraticModule{T <: Flag, U <: Flag, B <: AbstractFlagModel{U, N, D}, N, D} <: AbstractFlagModel{T, N, D}

Implements quadractic modules for inequalities. Meant to be used as a submodel of a `FlagModel`. Multiplies all elements of the `baseModel` with the `inequality` and then transforms them to type `T` (e.g. by unlabeling). The inequality `f >= 0` is given in form of a `QuantumFlag{U}` describing `f`. If both inequalities `f >= 0` and `-f >= 0` appear in the problem it is equivalent, but much more efficient, to use an `EqualityModule` instead.

# Parameters
- `T`: Target Flag type
- `U`: Flag type of the inequality, and the target type of the base model
- `B`: Type of the base model
- `N`: Limit parameter, see `AbstractFlagModel`
- `D`: Data type of coefficients of the final optimization problem

"""
mutable struct QuadraticModule{T<:Flag,U<:Flag,B,N,D} <:
               AbstractFlagModel{T,N,D} where {B<:AbstractFlagModel{U,N,D}}
    sdpData::Any
    baseModel::B
    inequality::QuantumFlag{U}
    reservedVerts::Int

    function QuadraticModule{T,U}(
        baseModel::B, inequality::QuantumFlag{U}, reservedVerts::Int=0
    ) where {T<:Flag,U<:Flag,N,D,B<:AbstractFlagModel{U,N,D}}
        return new{T,U,B,N,D}(Dict(), baseModel, inequality, reservedVerts)
    end

    function QuadraticModule{T}(
        baseModel::B, inequality::QuantumFlag{T}, reservedVerts::Int=0
    ) where {T<:Flag,N,D,B<:AbstractFlagModel{T,N,D}}
        return new{T,T,B,N,D}(Dict(), baseModel, inequality, reservedVerts)
    end
end

function computeSDP!(
    m::QuadraticModule{T,U,B,N,D}, reservedVerts::Int
) where {T<:Flag,U<:Flag,N,D,B<:AbstractFlagModel{U,N,D}}
    @info "computing ineq module"
    computeSDP!(m.baseModel, reservedVerts + m.reservedVerts)

    # @assert N == :limit "TODO"
    m.sdpData = Dict()
    for (G, data) in m.baseModel.sdpData
        tmp = QuantumFlag{T}(glueFinite(N - reservedVerts, G, m.inequality))
        noLabel = removeIsolated(tmp)
        # noLabel = removeIsolated(QuantumFlag{T}(G * m.inequality))

        GH = labelCanonically(noLabel)
        for (gh, cgh) in GH.coeff
            if !haskey(m.sdpData, gh)
                m.sdpData[gh] = Dict()
            end
            for (mu, blk) in data
                if !haskey(m.sdpData[gh], mu)
                    m.sdpData[gh][mu] = cgh * blk
                else
                    m.sdpData[gh][mu] += cgh * blk
                end
            end
        end
    end
end

function modelBlockSizes(m::QuadraticModule)
    return modelBlockSizes(m.baseModel)
end

function buildJuMPModel(m::QuadraticModule{T,U,B,N,D}, replaceBlocks=Dict(), jumpModel=Model()) where {T, U, B, N, D}
    b = modelBlockSizes(m)
    Y = Dict()
    constraints = Dict()
    for (mu, n) in b
        Y[mu] = get(replaceBlocks, mu) do
            name = "Y$mu"
            if n > 1
                v = @variable(jumpModel, [1:n, 1:n], Symmetric, base_name = name)
                constraints[name] = @constraint(jumpModel, v in PSDCone())
                return v
            else
                v = @variable(jumpModel, [1:1, 1:1], Symmetric, base_name = name)
                constraints[name] = @constraint(jumpModel, v .>= 0)
                return v
            end
        end
    end

    AT = typeof(sum(collect(values(Y))[1]))
    graphCoefficients = Dict()

    for G in keys(m.sdpData)
        # eG = AffExpr()
        # eG = GenericAffExpr{D, GenericVariableRef{D}}()
        eG = AT()
        for mu in keys(b)
            if haskey(m.sdpData[G], mu)
                for (i, j, c) in Iterators.zip(findnz(m.sdpData[G][mu])...)
                    i > j && continue
                    fact = (i == j ? D(1) : D(2))
                    add_to_expression!(eG, fact * D(c), Y[mu][i, j])
                    # add_to_expression!(eG, m.sdpData[G][mu][c],Y[mu][c])
                end
            end
        end
        graphCoefficients[G] = eG
    end
    # graphCoefficients = Dict(
    #     G => sum(
    #         dot(Y[mu], Symmetric(m.sdpData[G][mu])) for
    #         mu in keys(b) if haskey(m.sdpData[G], mu)
    #     ) for G in keys(m.sdpData)
    # )

    return (model=jumpModel, variables=graphCoefficients, blocks=Y, constraints=constraints)
end

function modelSize(m::QuadraticModule)
    return modelSize(m.baseModel)
end

"""
    EqualityModule{T<:Flag, U<:Flag, N, D} <: AbstractFlagModel{T, N, D}

Implements quadratic modules for equalities. Meant to be used as submodel of a `CompositeFlagModel`. Multiplies all elements of `basis`, a vector of all relevant Flags of type `U` with `equality`, converts the result to type `T`, and sets it to zero in the resulting optimization problem.
"""
mutable struct EqualityModule{T<:Flag,U<:Flag,N,D} <: AbstractFlagModel{T,N,D}
    sdpData::Any
    basis::Vector{U}
    equality::QuantumFlag{U}
    reservedVerts::Int

    function EqualityModule{T,U}(
        equality::QuantumFlag{U}, reservedVerts::Int=0
    ) where {T<:Flag,U<:Flag}
        return new{T,U,:limit,Int}(Dict(), U[], equality, reservedVerts)
    end
    function EqualityModule{T,U,N,D}(
        equality::QuantumFlag{U}, reservedVerts::Int=0
    ) where {T<:Flag,U<:Flag,N,D}
        return new{T,U,N,D}(Dict(), U[], equality, reservedVerts)
    end
end

function computeSDP!(
    m::EqualityModule{T,U,N,D}, reservedVerts::Int
) where {T<:Flag,U<:Flag,N,D}
    m.sdpData = Dict()
    @assert !(T isa InducedFlag) "TODO:"
    # @assert N == :limit "TODO"
    for (i, G) in enumerate(m.basis)
        for (G2, c) in m.equality.coeff
            # GG2 = G * G2
            GG2s = D(1) * glueFinite(N == :limit ? N : N - reservedVerts, G, G2)
            for (GG2, c2) in GG2s.coeff
                GG2 === nothing && continue
                if GG2 isa PartiallyLabeledFlag{T}
                    tmpG = D(c2) * label((GG2).F)[1]
                elseif true#GG2 isa T 
                    tmpG = D(c2) * labelCanonically(GG2)#[1]
                else
                    @show GG2
                    @show typeof(GG2)
                    error("Unhandled case")
                end
                for (H, c2) in tmpG.coeff
                    if !haskey(m.sdpData, H)
                        m.sdpData[H] = Dict()
                    end

                    m.sdpData[H][i] = get(m.sdpData[H], i, 0) + c * D(c2)
                end
            end
        end
    end
end

function modelBlockSizes(m::EqualityModule)
    return Dict(i => -1 for i in 1:length(m.basis))
end

function buildJuMPModel(m::EqualityModule{T,U,N,D}, replaceBlocks=Dict(), jumpModel=Model()) where {T,U,N,D}
    @assert length(replaceBlocks) == 0

    b = modelBlockSizes(m)
    Y = Dict()
    for (mu, n) in b
        Y[mu] = @variable(jumpModel)
    end

    # graphCoefficients = Dict(
    #     G => sum(Y[mu] * m.sdpData[G][mu] for mu in keys(b) if haskey(m.sdpData[G], mu)) for
    #     G in keys(m.sdpData)
    # )

    AT = typeof(sum(D(1)*collect(values(Y))[1]))
    graphCoefficients = Dict()

    for G in keys(m.sdpData)
        # eG = AffExpr()
        # eG = GenericAffExpr{D, GenericVariableRef{D}}()
        eG = AT()
        for mu in keys(b)
            if haskey(m.sdpData[G], mu)
                # for (i, j, c) in Iterators.zip(findnz(m.sdpData[G][mu])...)
                #     i > j && continue
                #     fact = (i == j ? D(1) : D(2))
                #     add_to_expression!(eG, fact * D(c), Y[mu][i, j])
                #     # add_to_expression!(eG, m.sdpData[G][mu][c],Y[mu][c])
                # end
                add_to_expression!(eG, m.sdpData[G][mu], Y[mu])
            end
        end
        graphCoefficients[G] = eG
    end

    return (model=jumpModel, variables=graphCoefficients, blocks=Y, constraints=Dict())
end

function modelSize(m::EqualityModule)
    return Partition(ones(Int, length(m.basis)))
end
