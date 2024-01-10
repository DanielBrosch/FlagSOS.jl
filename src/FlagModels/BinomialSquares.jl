export BinomialSquares

mutable struct BinomialSquares{T<:Flag,N,D} <: AbstractFlagModel{T,N,D}
    sdpData::Any
    # generators::Dict{Int,Vector{PartiallyLabeledFlag{T}}}
    basis::Vector{ProductFlag{NTuple{2,PartiallyColoredFlag{T}}}}

    function BinomialSquares{T,N,D}(maxVerts=0, maxEdges =0) where {T,N,D}
        res = new{T,N,D}(
            Dict(),
            # Dict{Int,Vector{PartiallyLabeledFlag{T}}}(),
            # Vector{Tuple{PartiallyLabeledFlag{T},PartiallyLabeledFlag{T}}}(),
            Vector{ProductFlag{NTuple{2,PartiallyColoredFlag{T}}}}(),
        )
        addGenerators!(res, maxVerts, maxEdges)
        return res
    end
end

function addGenerators!(m::BinomialSquares{T,N,D}, maxVerts, maxEdges) where {T,N,D}
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

    @warn "For truncation assumes edges are glued distinctly."

    coloredPairs = ProductFlag{NTuple{2,PartiallyColoredFlag{Graph}}}

    sameColors(x) = x.Fs[1].c == x.Fs[2].c

    for i in 1:maxVerts
        pairs = generateAll(
            coloredPairs,
            floor(Int, (maxVerts - i) / 2) + i,
            [[[i], floor(maxEdges/2)], [[i], floor(maxEdges/2)]];
            withProperty=sameColors,
        )
        filter!(x -> length(x.Fs[1].c) == i, pairs)
        filter!(x -> hash(x.Fs[1]) <= hash(x.Fs[2]), pairs)
        m.basis = vcat(m.basis, pairs)
    end
end

function computeSDP!(m::BinomialSquares{T,N,D}, reservedVerts::Int) where {T<:Flag,N,D}
    @assert N == :limit "TODO: Finite binomial squares (and reserved verts)"
    for F in m.basis
        F2 = labelCanonically((F.Fs[1] * F.Fs[1]).F)
        G2 = labelCanonically((F.Fs[2] * F.Fs[2]).F)
        FG = labelCanonically((F.Fs[1] * F.Fs[2]).F)

        e = D(1) * F2 - D(2) * FG + D(1) * G2

        for (G, c) in e.coeff
            if !haskey(m.sdpData, G)
                m.sdpData[G] = Dict()
            end
            if !haskey(m.sdpData[G], F)
                m.sdpData[G][F] = 0
            end
            m.sdpData[G][F] += c
        end
    end
end

function modelBlockSizes(m::BinomialSquares)
    return Dict(p => 1 for p in m.basis)
end

function buildJuMPModel(
    m::BinomialSquares{T,N,D}, replaceBlocks=Dict(), jumpModel=Model()
) where {T,N,D}
    @assert length(replaceBlocks) == 0

    b = modelBlockSizes(m)
    Y = Dict()
    for (mu, _) in b
        Y[mu] = @variable(jumpModel)
    end

    # graphCoefficients = Dict(
    #     G => sum(Y[mu] * m.sdpData[G][mu] for mu in keys(b) if haskey(m.sdpData[G], mu)) for
    #     G in keys(m.sdpData)
    # )

    AT = typeof(sum(D(1) * collect(values(Y))[1]))
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

function modelSize(m::BinomialSquares)
    return [1 for _ in m.basis]
end