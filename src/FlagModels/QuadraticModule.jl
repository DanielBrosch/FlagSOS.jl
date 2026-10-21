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

function Base.show(io::IO, m::QuadraticModule{T,U,B,N,D}) where {T,U,B,N,D}
    println(io, "Quadratic module for inequality $(m.inequality)>=0\nWith base model:")
    return println(io, m.baseModel)
end

function roundResults(
    m::QuadraticModule{T,U,B,N,D}, jumpModel, variables, blocks, constraints; prec=1e-5
) where {T,U,N,D,B}
    return roundResults(m.baseModel, jumpModel, variables, blocks, constraints)
end

# Products reuse the same outer flags for many multipliers. Convert, unlabel,
# and (if necessary) lift each outer flag once per module, retaining its exact
# averaging factor. Accumulate coefficients directly instead of repeatedly
# copying growing quantum-flag dictionaries with `sum`.
function _quadratic_product(
    G::U, inequality::QuantumFlag{U,C}, population, parent,
    images::Dict{U,QuantumFlag{T,Rational{Int}}}, lift_order,
) where {T,U,C}
    R = promote_type(C, Rational{Int})
    product = QuantumFlag{U,R}()
    for (H, c) in inequality.coeff
        iszero(c) && continue
        for (F, d) in glueFinite(population, G, H; base_model=parent).coeff
            product.coeff[F] = get(product.coeff, F, zero(R)) + c * d
        end
    end

    result = QuantumFlag{T,R}()
    for (F, c) in product.coeff
        iszero(c) && continue
        image = get!(images, F) do
            converted = QuantumFlag{T}(1 // 1 * F)
            if lift_order !== nothing
                converted = add_verts(parent, converted, lift_order)
            end
            labelCanonically(converted)
        end
        for (H, d) in image.coeff
            result.coeff[H] = get(result.coeff, H, zero(R)) + c * d
        end
    end
    filter!(p -> !iszero(p.second), result.coeff)
    return result
end

# A function barrier specializes updates even when the surrounding SDP
# dictionary has abstract key/value types.
function _add_quadratic_block!(target, coefficient, block)
    target .+= coefficient .* block
    return target
end

function _add_quadratic_block!(target::SparseMatrixCSC, coefficient, block::SparseMatrixCSC)
    axes(target) == axes(block) || throw(DimensionMismatch("Incompatible SDP block sizes"))
    rows, entries = rowvals(block), nonzeros(block)
    # Sparse broadcast may copy the growing destination to handle aliasing.
    # Visit only the source entries; previously accumulated entries stay put.
    for col in axes(block, 2), p in nzrange(block, col)
        value = coefficient * entries[p]
        iszero(value) && continue
        row = rows[p]
        target[row, col] += value
    end
    return target
end

function computeSDP!(
    m::QuadraticModule{T,U,B,N,D}, reservedVerts::Int
) where {T<:Flag,U<:Flag,N,D,B<:AbstractFlagModel{U,N,D}}
    @info "computing ineq module for $(m.inequality)"
    computeSDP!(m.baseModel, reservedVerts + m.reservedVerts)

    population = N == :limit ? N : N - reservedVerts
    cache_images = isInducedFlag(T) && isInducedFlag(U) && is_up_to_iso(U)
    images = Dict{U,QuantumFlag{T,Rational{Int}}}()
    lift_order = N != :limit && m.baseModel isa RazborovModel && isInducedFlag(T) ?
        m.baseModel.lvl + free_verts(m.inequality) : nothing
    m.sdpData = Dict()
    for (G, data) in m.baseModel.sdpData
        if cache_images
            GH = _quadratic_product(
                G, m.inequality, population, m.baseModel.parentModel, images, lift_order,
            )
        else
            tmp = QuantumFlag{T}(glueFinite(
                population, G, m.inequality; base_model=m.baseModel.parentModel,
            ))
            if lift_order !== nothing
                tmp = add_verts(m.baseModel.parentModel, tmp, lift_order)
            end
            GH = labelCanonically(isInducedFlag(T) ? tmp : removeIsolated(tmp))
        end
        for (gh, cgh) in GH.coeff
            blocks = get!(m.sdpData, gh) do
                Dict()
            end
            for (mu, blk) in data
                if !haskey(blocks, mu)
                    blocks[mu] = cgh * blk
                elseif cache_images
                    _add_quadratic_block!(blocks[mu], cgh, blk)
                else
                    blocks[mu] += cgh * blk
                end
            end
        end
    end
end

function modelBlockSizes(m::QuadraticModule)
    return modelBlockSizes(m.baseModel)
end

function buildJuMPModel(
    m::QuadraticModule{T,U,B,N,D}, replaceBlocks=Dict(), jumpModel=Model()
) where {T,U,B,N,D}
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

    if length(Y) > 0
        AT = typeof(sum(collect(values(Y))[1]))
    end
    # AT = GenericAffExpr{D, GenericVariableRef{D}}
    # AT = GenericAffExpr{D, GenericVariableRef{D}}
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
                    # @show typeof(eG)
                    # @show typeof(fact*D(c))
                    # @show typeof(Y[mu][i,j])
                    # @show AT
                    # @show typeof(sum(collect(values(Y))[1]))
                    # @show c
                    # @show Y[mu]
                    add_to_expression!(eG, fact * D(c), D(1) * Y[mu][i, j])
                    # eG += fact*D(c)*Y[mu][i,j]
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

Implements quadratic modules for equalities. Meant to be used as submodel of a `FlagModel`. Multiplies all elements of `basis`, a vector of all relevant Flags of type `U` with `equality`, converts the result to type `T`, and sets it to zero in the resulting optimization problem.

The optional constructor keyword `parent` supplies the containing `FlagModel`
for forbidden-flag filtering and product caching. Induced columns are computed
at a common vertex order; the containing model lifts them further if needed.
"""
mutable struct EqualityModule{T<:Flag,U<:Flag,N,D} <: AbstractFlagModel{T,N,D}
    sdpData::Any
    basis::Vector{U}
    equality::QuantumFlag{U}
    reservedVerts::Int
    parentModel::Any

    function EqualityModule{T,U}(
        equality::QuantumFlag{U}, reservedVerts::Int=0; parent=nothing
    ) where {T<:Flag,U<:Flag}
        return new{T,U,:limit,Int}(Dict(), U[], equality, reservedVerts, parent)
    end
    function EqualityModule{T,U,N,D}(
        equality::QuantumFlag{U}, reservedVerts::Int=0; parent=nothing
    ) where {T<:Flag,U<:Flag,N,D}
        return new{T,U,N,D}(Dict(), U[], equality, reservedVerts, parent)
    end
end

function roundResults(
    m::EqualityModule{T,U,N,D}, jumpModel, variables, blocks, constraints; prec=1e-5
) where {T,U,N,D}
    ex = Dict()

    den = round(BigInt, 1 / prec)
    function roundDen(x)
        return round(BigInt, den * x) // den
    end

    for (mu, b) in blocks
        # ex[mu] = rationalize(BigInt, value(b); tol=prec)#; digits = digits)
        ex[mu] = roundDen(value(b))
    end

    return ex
end

function Base.show(io::IO, m::EqualityModule{T,U,N,D}) where {T,U,N,D}
    return println(
        io,
        "Equality constraint ($(m.equality) == 0) multiplied with $(length(m.basis)) flags.",
    )
end

function computeSDP!(
    m::EqualityModule{T,U,N,D}, reservedVerts::Int
) where {T<:Flag,U<:Flag,N,D}
    m.sdpData = Dict()
    isempty(m.basis) && return nothing
    isempty(m.equality.coeff) && return nothing
    population = N == :limit ? N : N - reservedVerts
    # Asking the sampler for a common outer order retains finite-population
    # collisions while expressing every column in the same density basis.
    product_options = if isInducedFlag(U)
        (n_outer=maximum(free_verts, m.basis) + size(m.equality),)
    else
        NamedTuple()
    end
    for (i, G) in enumerate(m.basis)
        for (G2, c) in m.equality.coeff
            GG2s = D(1) * glueFinite(
                population, G, G2; base_model=m.parentModel, product_options...
            )
            for (GG2, c2) in GG2s.coeff
                GG2 === nothing && continue
                if GG2 isa PartiallyLabeledFlag{T}
                    tmpG = D(c2) * labelCanonically(unlabel(GG2))
                else
                    tmpG = D(c2) * labelCanonically(GG2)
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

function buildJuMPModel(
    m::EqualityModule{T,U,N,D}, replaceBlocks=Dict(), jumpModel=Model()
) where {T,U,N,D}
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

    if length(Y) > 0
        AT = typeof(sum(D(1) * collect(values(Y))[1]))
    end
    # AT = GenericAffExpr{D,GenericVariableRef{D}}
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

function verifySOS(m::EqualityModule, sol::Dict; io::IO=stdout)
    println(io, "Equality module coming from constraint")
    println(io, "$(m.equality)= 0")
    for i in keys(sol)
        if sol[i] != 0 // 1
            println(io, "Times $(sol[i])$(m.basis[i]) :")
            print(
                io,
                sum(m.sdpData) do (G, B)
                    sum(B) do (j, c)
                        j != i && return 0 * one(G)
                        get(sol, j, 0 // 1) * c * G
                    end
                end,
            )
            println(io, "= 0")
        end
    end
    res = sum(m.sdpData) do (G, B)
        sum(B) do (i, c)
            get(sol, i, 0 // 1) * c * G
        end
    end
    println(io, "Equality module result:")
    println(io, "$(res)= 0")
    println(io)
    return res
end

function verifySOS(
    m::QuadraticModule{T,U,B,N,D}, sol::Dict; io::IO=stdout
) where {T,U,B,N,D}
    println(io, "Quadratic module coming from constraint")
    println(io, "$(m.inequality)>= 0")
    println(io, "With base model:")
    res = verifySOS(m.baseModel, sol; io=io)

    res = labelCanonically(typeof(res)(m.inequality) * res)

    if io !== nothing
        println(io, "\nQuadratic module result:")
        println(io, "$(res)>= 0")
        println(io)
    end

    return res
end
