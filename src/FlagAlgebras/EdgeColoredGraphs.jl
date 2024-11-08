export EdgeColoredGraph

""" 
    $(TYPEDEF)

A model of an edge colored graph, given by its adjacency matrix. `N`: Number of colors, `-1` for infinite. `B`: Bool for colorblind.
"""
struct EdgeColoredGraph{N,B} <: Flag
    A::Symmetric{Int,Matrix{Int}}

    function EdgeColoredGraph{N,B}(A::Matrix{Int}) where {N,B}
        B && sortEntries!(A)
        return new{N,B}(Symmetric(A))
    end
    function EdgeColoredGraph{N,B}(A::Symmetric{Int,Matrix{Int}}) where {N,B}
        B && (A = Symmetric(sortEntries!(Matrix(A))))
        return new{N,B}(A)
    end
    function EdgeColoredGraph{N,B}() where {N,B}
        return new{N,B}(Symmetric(Matrix{Int}(undef, 0, 0)))
    end
end

function highestColor(F::EdgeColoredGraph)
    return maximum(F.A; init=0)
end

# In the colorblind setting the colors should always be `1...highestColor(F)` and the non-edge 0. The colors should appear in this order for the first time.
function sortEntries!(A::Matrix{Int})
    cs::Vector{Int} = unique(A)
    filter!(x -> x != 0, cs)
    translate = Dict{Int,Int}(c => i for (i, c) in enumerate(cs))
    translate[0] = 0
    map!(c -> translate[c], A, A)
    return A
end

function Base.show(io::IO, G::EdgeColoredGraph{N,B}) where {N,B}
    if size(G.A, 1) == 0
        print(io, "∅ ")
    else
        print(io, "($(size(G.A,1)),")
        for c in unique(G.A)
            c == 0 && continue
            first = true
            if !B
                print(io, " c$c:")
            else
                print(io, "{")
            end
            for e in eachindex(G.A)
                if e[1] <= e[2] && G.A[e] == c
                    (!B || !first) && print(io, " ")
                    print(io, "$(e[1])-$(e[2])")
                    first = false
                end
            end
            B && print(io, "}")
        end
        print(io, ")")
    end
end

import Base.==
function ==(A::EdgeColoredGraph, B::EdgeColoredGraph)
    return A.A == B.A
end
import Base.hash
function hash(A::EdgeColoredGraph, h::UInt)
    return hash(A.A, hash(:EdgeColoredGraph, h))
end

Base.one(::Type{EdgeColoredGraph{N,B}}) where {N,B} = EdgeColoredGraph{N,B}()

function size(G::EdgeColoredGraph)::Int
    return size(G.A, 1)
end

struct ColoredEdgePredicate <: Predicate
    i::Int
    j::Int
    c::Int # -c for all colors bigger than c
    ColoredEdgePredicate(i, j, c) = new(min(i, j), max(i, j), c)
end

function isAllowed(G::EdgeColoredGraph{N,B}, e::ColoredEdgePredicate) where {N,B}
    N > -1 && -e.c >= N && return false
    c = G.A[e.i, e.j]
    c == 0 && return true
    if e.c > 0
        return c == e.c
    else
        return c > -e.c
    end
end

function predicateType(::Type{EdgeColoredGraph{N,B}}) where {N,B}
    return ColoredEdgePredicate
end

function hash(P::ColoredEdgePredicate, h::UInt)
    return hash(P.i, hash(P.j, hash(P.c, hash(:ColoredEdgePredicate, h))))
end
function ==(A::ColoredEdgePredicate, B::ColoredEdgePredicate)
    return A.i == B.i && A.j == B.j && A.c == B.c
end

function permute(pred::ColoredEdgePredicate, p::AbstractVector{Int}) where {N}
    return ColoredEdgePredicate(p[pred.i], p[pred.j], pred.c)
end

# not needed? Permutation should normally change colors, but here this just permutes the list of predicates for the missing edges. So it should not change anything.
# function permute(
#     pred::ColoredEdgePredicate,
#     p::AbstractVector{Int},
#     G::EdgeColoredGraph{N,true},
#     Gp::EdgeColoredGraph{N,true},
# ) where {N}
#     if pred.c == -1
#         return ColoredEdgePredicate(p[pred.i], p[pred.j], pred.c)
#     end
#     posBefore = findfirst(x->x == pred.c, G.A)
#     @assert posBefore !== nothing
#     newC = Gp.A[p[posBefore[1]], p[posBefore[2]]]
#     return ColoredEdgePredicate(p[pred.i], p[pred.j], newC)
# end

function findUnknownPredicates(
    F::EdgeColoredGraph{N,B}, fixed::Vector{U}, predLimits::Vector
)::Vector{Vector{ColoredEdgePredicate}} where {U<:AbstractVector{Int},N,B}
    @assert length(predLimits) in [0, 1]
    res = ColoredEdgePredicate[]
    if length(predLimits) == 1 && countEdges(F)[1] >= predLimits[1]
        return [res]
    end

    hC = highestColor(F)

    needsMoreColors = N == -1 || hC < N

    for e in combinations(1:size(F), 2)
        if (F.A[e[1], e[2]] == 0) && !any(issubset(e, f) for f in fixed)
            needsMoreColors && push!(res, ColoredEdgePredicate(e..., -hC))
            for c in 1:hC
                c == 0 && continue
                push!(res, ColoredEdgePredicate(e..., c))
            end
        end
    end
    return [res]
end

# function findUnknownGenerationPredicates(
#     F::EdgeColoredGraph, fixed::Vector{U}=Vector{Int}[], predLimits::Vector=Int[]
# ) where {U<:AbstractVector{Int}}
#     return findUnknownPredicates(F, fixed, predLimits)
# end

function addPredicates(
    G::EdgeColoredGraph{N,B}, preds::Vector{ColoredEdgePredicate}
) where {N,B}
    if length(preds) == 0
        return [G]
    end

    p = preds[1]
    res = EdgeColoredGraph{N,B}[]
    G.A[p.i, p.j] != 0 && return res

    hC = highestColor(G)
    # for p in preds
    nC = Int[p.c]
    if p.c <= 0
        nC = collect((-p.c+1):(hC+1))
    end

    for c in nC
        N > -1 && c > N && continue
        A = Matrix(G.A)
        A[p.i, p.j] = c

        G2 = EdgeColoredGraph{N,B}(A)

        if length(preds) > 1
            res = vcat(res, addPredicates(G2, preds[2:end]))
        else
            push!(res, G2)
        end
    end

    return res
end

# apply p to g1, then glue together
function glue(
    g1::EdgeColoredGraph{N,false}, g2::EdgeColoredGraph{N,false}, p::AbstractVector{Int}
) where {N}
    n1 = size(g1)
    n2 = size(g2)
    n = max(n2, length(p) > 0 ? maximum(p) : 0)

    res = zeros(Int, n, n)
    res[1:n2, 1:n2] = g2.A

    for i in 1:n1, j in 1:n1
        g1.A[i, j] == 0 && continue
        if res[p[i], p[j]] != 0 && res[p[i], p[j]] != g1.A[i, j]
            return nothing
        end
        res[p[i], p[j]] = g1.A[i, j]
    end

    return EdgeColoredGraph{N,false}(res)
end

function glue(
    g1::EdgeColoredGraph{N,true}, g2::EdgeColoredGraph{N,true}, p::AbstractVector{Int}
) where {N}
    n1 = size(g1)
    n2 = size(g2)
    n = max(n2, length(p) > 0 ? maximum(p) : 0)

    hC = highestColor(g2)
    colorTranslate = Dict{Int,Int}(i => -1 for i in 1:highestColor(g1))

    ov = [i for i in 1:n1 if p[i] <= n2]
    for i in ov, j in ov
        c1 = g1.A[i, j]
        c2 = g2.A[p[i], p[j]]
        if c2 != 0
            if colorTranslate[c1] == -1
                colorTranslate[c1] = c2
            elseif colorTranslate[c1] != c2
                return nothing
            end
        end
    end

    for (c, cT) in colorTranslate
        if cT == -1
            hC += 1
            colorTranslate[c] = hC
        end
    end

    N > -1 && hC > N && return nothing

    res = zeros(Int, n, n)
    res[1:n2, 1:n2] = g2.A

    for i in 1:n1, j in 1:n1
        g1.A[i, j] == 0 && continue

        res[p[i], p[j]] = colorTranslate[g1.A[i, j]]
    end

    return EdgeColoredGraph{N,true}(res)
end

# function glue(Gs::Vararg{EdgeColoredGraph})::EdgeColoredGraph
#     if length(Gs) == 1
#         return Gs[1]
#     elseif length(Gs) == 2
#         return glue(Gs..., 1:size(Gs[1]))
#     end

#     n = size(Gs[1])
#     res::BitMatrix = BitMatrix(zeros(n, n))

#     for g in Gs
#         res .|= g.A

#         # Character Flags
#         # res .⊻= g.A
#         # nZs = vec(sum(res, dims=1) .> 0)
#         # res = res[nZs, nZs]
#     end

#     return EdgeColoredGraph(Symmetric(res))
# end

# check if swapping v1 and v2 leaves g invariant
function isSym(g::EdgeColoredGraph, v1::Int, v2::Int)::Bool
    n = size(g)
    p = collect(1:n)
    p[v2] = v1
    p[v1] = v2
    Ap = sortEntries!(g.A[p, p])
    return g.A == Ap
end

# function toNonInduced(G)
#     fact = 1 #Int64(factorial(length(G)) / aut(G).size) # number of ways to embed g 

#     zs = filter!(x -> x[1] < x[2], findall(G.A .== 0))

#     tmp = Dict([labelCanonically(G) => fact])

#     for newEs in combinations(zs)
#         newG = BitMatrix(copy(G.A))
#         for e in newEs
#             newG[e[1], e[2]] = 1
#             newG[e[2], e[1]] = 1
#         end
#         tmp[EdgeColoredGraph(newG)] = (-1)^(length(newEs)) * fact
#     end

#     res = Dict()
#     newGs = collect(keys(tmp))
#     newGsLabelled = labelCanonically(newGs)

#     for i in 1:length(newGs)
#         if !haskey(res, newGsLabelled[i])
#             res[newGsLabelled[i]] = tmp[newGs[i]]
#         else
#             res[newGsLabelled[i]] += tmp[newGs[i]]
#         end
#     end

#     return res
# end

function subFlag(
    F::EdgeColoredGraph{N,B}, vertices::AbstractVector{Int}
)::EdgeColoredGraph{N,B} where {N,B}
    return EdgeColoredGraph{N,B}(F.A[vertices, vertices])
end

function maxPredicateArguments(::Type{EdgeColoredGraph})
    return 2
end

function distinguish(F::EdgeColoredGraph, v::Int, W::BitVector)::UInt
    cs = unique(F.A[W, v])
    counts = sort!([length(findall(x -> x == c, F.A[W, v])) for c in cs])
    @inbounds return hash(counts)
end

function distinguish(F::ColoredEdgePredicate, v::Int, W::BitVector)::UInt
    return hash((v == F.i && W[F.j]) || (v == F.j && W[F.i]), hash(F.c))
end

function countEdges(F::EdgeColoredGraph)::Vector{Int}
    return [Int(sum(F.A .!= 0) / 2)]
end

function isolatedVertices(F::EdgeColoredGraph)::BitVector
    # res = BitVector(zeros(Bool, size(F)))
    res = BitArray(undef, size(F))
    any!(res, F.A .!= 0)
    map!(!, res, res)
    # return .!vec(any(F.A; dims=1))
    return res
end
