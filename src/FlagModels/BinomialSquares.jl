export BinomialSquares

mutable struct BinomialSquares{T<:Flag,N,D} <: AbstractFlagModel{T,N,D}
    sdpData::Any
    generators::Dict{Int,Vector{PartiallyLabeledFlag{T}}}
    basis::Vector{ProductFlag{NTuple{2,PartiallyColoredFlag{T}}}}

    function BinomialSquares{T,N,D}(lvl=0) where {T,N,D}
        res = new{T,N,D}(
            Dict(),
            Dict{Int,Vector{PartiallyLabeledFlag{T}}}(),
            # Vector{Tuple{PartiallyLabeledFlag{T},PartiallyLabeledFlag{T}}}(),
            Vector{ProductFlag{NTuple{2,PartiallyColoredFlag{T}}}}()
        )
        addGenerators!(res, lvl)
        return res
    end
end

function addGenerators!(m::BinomialSquares{T,N,D}, lvl) where {T,N,D}
    # PT = PartiallyLabeledFlag{T}

    # for i = 1:lvl 
    #     list = generateAll(PT, floor(Int, (lvl - i)/2) + i, [i, 9999])
    #     filter!(x->x.n == i, list)
    #     m.generators[i] = list
    # end

    # for i = 1:lvl 
    #     for (F,G) in combinations(m.generators[i], 2)
    #         push!(m.basis, (F,G))
    #     end
    # end

    #TODO: Too many graphs! Use partially colored flags instead of partially labeled, and label the direct product flag (F,G)

    coloredPairs = ProductFlag{NTuple{2,PartiallyColoredFlag{Graph}}}

    sameColors(x) = x.Fs[1].c == x.Fs[2].c

    for i = 1:lvl 
        pairs = generateAll(
            coloredPairs, floor(Int, (lvl - i)/2) + i, [[[i], 99], [[i], 99]]; withProperty=sameColors
        )
        filter!(x->length(x.Fs[1].c) == i, pairs)
        filter!(x->hash(x.Fs[1]) <= hash(x.Fs[2]), pairs)
        m.basis = vcat(m.basis, pairs)
    end
end

function computeSDP!(m::BinomialSquares{T,N,D}, reservedVerts::Int) where {T<:Flag,N,D}
end

function modelBlockSizes(m::BinomialSquares)
    return Dict(p => 1 for p in m.basis)
end

function buildJuMPModel(
    m::BinomialSquares{T,N,D}, replaceBlocks=Dict(), jumpModel=Model()
) where {T,N,D}
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

function modelSize(m::BinomialSquares)
    return [1 for _ in m.basis]
end