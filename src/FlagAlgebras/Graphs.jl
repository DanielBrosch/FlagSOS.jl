export Graph, connectedComponents

""" 
    $(TYPEDEF)

A model of a graph, given by its adjacency matrix.
"""
struct Graph <: Flag
    A::Symmetric{Bool,BitMatrix}

    Graph(A::Matrix{Bool}) = new(Symmetric(BitMatrix(A)))
    Graph(A::Symmetric{Bool,BitMatrix}) = new(A)
    Graph(A::BitMatrix) = new(Symmetric(A))
    Graph() = new(Symmetric(BitMatrix(undef, 0, 0)))
end

function Base.show(io::IO, G::Graph)
    if size(G.A,1) == 0
        print(io, "∅ ")
    else
        print(io, "($(size(G.A,1)),")
        first = true 
        for c in eachindex(G.A)
            if c[1] <= c[2] && G.A[c]
                if !first 
                    print(io, " ")
                end
                print(io, "$(c[1])-$(c[2])")
                first = false
            end
        end
        print(io, ")")
    end
end

import Base.==
function ==(A::Graph, B::Graph)
    return A.A == B.A
end
import Base.hash
function hash(A::Graph, h::UInt)
    return hash(A.A, hash(:Graph, h))
end

Base.one(::Type{Graph}) = Graph()

function size(G::Graph)::Int
    return size(G.A, 1)
end

struct EdgePredicate <: Predicate
    i::Int
    j::Int
    EdgePredicate(i, j) = new(min(i, j), max(i, j))
end

function predicateType(::Type{Graph})
    return EdgePredicate
end

function hash(P::EdgePredicate, h::UInt)
    return hash(P.i, hash(P.j, hash(:EdgePredicate, h)))
end
function ==(A::EdgePredicate, B::EdgePredicate)
    return A.i == B.i && A.j == B.j
end

function permute(pred::EdgePredicate, p::AbstractVector{Int})
    return EdgePredicate(p[pred.i], p[pred.j])
end

function findUnknownPredicates(
    F::Graph, fixed::Vector{U}, predLimits::Vector
)::Vector{Vector{EdgePredicate}} where {U<:AbstractVector{Int}}
    @assert length(predLimits) in [0, 1]
    res = EdgePredicate[]
    if length(predLimits) == 1 && countEdges(F)[1] >= predLimits[1]
        return [res]
    end
    for e in combinations(1:size(F), 2)
        if (!F.A[e[1], e[2]]) && !any(issubset(e, f) for f in fixed)
            push!(res, EdgePredicate(e...))
        end
    end
    return [res]
end

# function findUnknownGenerationPredicates(
#     F::Graph, fixed::Vector{U}=Vector{Int}[], predLimits::Vector=Int[]
# ) where {U<:AbstractVector{Int}}
#     return findUnknownPredicates(F, fixed, predLimits)
# end

function addPredicates(G::Graph, preds::Vector{EdgePredicate})
    A = Matrix(copy(G.A))
    for p in preds
        A[p.i, p.j] = 1
    end
    return Graph(A)
end

# apply p to g1, then glue together
function glue(g1::Graph, g2::Graph, p::AbstractVector{Int})::Graph
    n1 = size(g1)
    n2 = size(g2)
    n = max(n2, length(p) > 0 ? maximum(p) : 0)

    res = BitMatrix(zeros(n, n))
    res[1:n2, 1:n2] = g2.A

    res[p[1:n1], p[1:n1]] .|= g1.A

    # Character Flags
    # res[p[1:n1],p[1:n1]] .⊻= g1.A
    # nZs = vec(sum(res, dims=1) .> 0)
    # res = res[nZs, nZs]

    return Graph(Symmetric(res))
end

function glue(Gs::Vararg{Graph})::Graph
    if length(Gs) == 1
        return Gs[1]
    elseif length(Gs) == 2
        return glue(Gs..., 1:size(Gs[1]))
    end

    n = size(Gs[1])
    res::BitMatrix = BitMatrix(zeros(n, n))

    for g in Gs
        res .|= g.A

        # Character Flags
        # res .⊻= g.A
        # nZs = vec(sum(res, dims=1) .> 0)
        # res = res[nZs, nZs]
    end

    return Graph(Symmetric(res))
end

# check if swapping v1 and v2 leaves g invariant
function isSym(g::Graph, v1::Int, v2::Int)::Bool
    n = size(g)
    return g.A[v1, setdiff(1:n, [v1, v2])] == g.A[v2, setdiff(1:n, [v1, v2])]
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
#         tmp[Graph(newG)] = (-1)^(length(newEs)) * fact
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

function subFlag(F::Graph, vertices::AbstractVector{Int})::Graph
    return Graph(F.A[vertices, vertices])
end

function maxPredicateArguments(::Type{Graph})
    return 2
end

function isBipartite(F::Graph)
    n = size(F)

    n < 3 && return true

    # Attempt to 2-color (+-1)
    colors = zeros(n)
    colors[1] = 1
    notDone = ones(Bool, n)

    while any(notDone)
        i = findfirst(notDone .&& (colors .!= 0))

        if i === nothing
            j = findfirst(notDone)
            colors[j] = 1
        else
            neighbors = [j for j in 1:n if i != j && F.A[i, j]]
            if any(colors[neighbors] .== colors[i])
                return false
            end
            colors[neighbors] .= -colors[i]
            notDone[i] = false
        end
    end

    return true
end

function distinguish(F::Graph, v::Int, W::BitVector)::UInt
    @inbounds return hash(sum(F.A[W, v]))
end

function distinguish(F::EdgePredicate, v::Int, W::BitVector)::UInt
    return hash((v == F.i && W[F.j]) || (v == F.j && W[F.i]))
end

function countEdges(F::Graph)::Vector{Int}
    return [Int(sum(F.A) / 2)]
end

function isolatedVertices(F::Graph)::BitVector
    # res = BitVector(zeros(Bool, size(F)))
    res = BitArray(undef, size(F))
    any!(res, F.A)
    map!(!, res, res)
    # return .!vec(any(F.A; dims=1))
    return res
end

function connectedComponents(G::Graph)::Vector{Graph}
    n = size(G)

    if n == 0
        return [G]
    end

    components = zeros(Int, n)
    nComp = 0
    for i = 1:n
        if components[i] == 0
            nComp += 1
            components[i] = nComp
        end
        for j = i+1:n
            if G.A[i,j] == 1
                if components[j] == 0
                    components[j] = components[i]
                else
                    c = minimum(components[[i,j]])
                    d = maximum(components[[i,j]])
                    components[components.==d] .= c
                end
            end
        end
    end
    return [subFlag(G, findall(x->x==u, components)) for u in unique(components)]
end