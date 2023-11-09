export DirectedGraph

""" 
    $(TYPEDEF)

A model of a directed graph, given by its adjacency matrix.
"""
struct DirectedGraph{allowDigons} <: Flag
    A::BitMatrix

    DirectedGraph(A::Matrix{Bool}) = new{false}(BitMatrix(A))
    DirectedGraph(A::BitMatrix) = new{false}(A)
    DirectedGraph() = new{false}(BitMatrix(undef, 0, 0))

    DirectedGraph{false}(A::Matrix{Bool}) = new{false}(BitMatrix(A))
    DirectedGraph{false}(A::BitMatrix) = new{false}(A)
    DirectedGraph{false}() = new{false}(BitMatrix(undef, 0, 0))
end

import Base.==
function ==(A::DirectedGraph, B::DirectedGraph)
    return A.A == B.A
end
import Base.hash
function hash(A::DirectedGraph, h::UInt)
    return hash(A.A, hash(:DirectedGraph, h))
end

isAllowed(A::DirectedGraph{true}) = true

function isAllowed(A::DirectedGraph{false})
    n = size(A)
    for i in 1:n
        for j in (i + 1):n
            if A.A[i, j] && A.A[j, i]
                return false
            end
        end
    end
    return true
end

function Base.one(::Type{DirectedGraph{allowDigons}}) where {allowDigons}
    return DirectedGraph{allowDigons}()
end

Base.one(::Type{DirectedGraph}) = one(DirectedGraph{false})

function size(G::DirectedGraph)::Int
    return size(G.A, 1)
end

struct DirectedEdgePredicate <: Predicate
    i::Int
    j::Int
    DirectedEdgePredicate(i, j) = new(i, j)
end

function isAllowed(F::DirectedGraph{false}, P::DirectedEdgePredicate)
    return !F.A[P.j, P.i]
end

function predicateType(::Type{DirectedGraph{F}}) where {F}
    return DirectedEdgePredicate
end

function findUnknownPredicates(
    F::DirectedGraph{allowDigons}, fixed::Vector{U}, predLimits::Vector{Int}
)::Vector{Vector{DirectedEdgePredicate}} where {U<:AbstractVector{Int},allowDigons}
    res = DirectedEdgePredicate[]
    for e in Iterators.product(1:size(F), 1:size(F))
        if e[1] != e[2] &&
            (!F.A[e...]) &&
            !any(issubset(e, f) for f in fixed) &&
            (allowDigons == Val(true) || !F.A[e[2], e[1]])
            push!(res, DirectedEdgePredicate(e...))
        end
    end
    return [res]
end

function addPredicates(
    G::DirectedGraph{allowDigons}, preds::Vector{DirectedEdgePredicate}
) where {allowDigons}
    A = deepcopy(G.A)
    for p in preds
        @assert p.i <= size(A, 1)
        @assert p.j <= size(A, 2)
        allowDigons == false && A[p.j, p.i] == 1 && return nothing
        A[p.i, p.j] = 1
    end
    return DirectedGraph{allowDigons}(A)
end

# apply p to g1, then glue together
function glue(
    g1::DirectedGraph{allowDigons}, g2::DirectedGraph{allowDigons}, p::AbstractVector{Int}
) where {allowDigons}
    n1 = size(g1)
    n2 = size(g2)
    n = max(n2, length(p) > 0 ? maximum(p) : 0)

    # res = BitMatrix(zeros(Bool, n, n))
    res = BitMatrix(undef, n, n)
    @views res[1:n2, 1:n2] = g2.A
    @views res[p[1:n1], p[1:n1]] .|= g1.A

    res = DirectedGraph{allowDigons}(res)
    !isAllowed(res) && return nothing
    return res
end

function glue(Gs::Vararg{DirectedGraph{allowDigons}}) where {allowDigons}
    if length(Gs) == 1
        return Gs[1]
    elseif length(Gs) == 2
        return glue(Gs..., 1:size(Gs[1]))
    end

    n = size(Gs[1])
    res::BitMatrix = BitMatrix(zeros(n, n))

    for g in Gs
        res .|= g.A
    end

    res = DirectedGraph{allowDigons}(res)
    !isAllowed(res) && return nothing
    return res
end

# check if swapping v1 and v2 leaves g invariant
function isSym(g::DirectedGraph, v1::Int, v2::Int)::Bool
    n = size(g)
    p = collect(1:n)
    p[v1] = v2
    p[v2] = v1
    @views return g.A[p, p] == g.A
end

function subFlag(F::DirectedGraph, vertices::AbstractVector{Int})::DirectedGraph
    return DirectedGraph(F.A[vertices, vertices])
end

function maxPredicateArguments(::Type{DirectedGraph})
    return 2
end

function maxPredicateArguments(::Type{DirectedGraph{allowDigons}}) where {allowDigons}
    return 2
end

function distinguish(F::DirectedGraph, v::Int, W::BitVector)::UInt
    eout = 0
    ein = 0
    for i in eachindex(W)
        if W[i]
            eout += F.A[i, v]
            ein += F.A[v, i]
        end
    end
    return hash(eout, hash(ein))
    # return hash((sum(F.A[i, v] for i in findall(W)), sum(F.A[v, i] for i in findall(W))))
end

function distinguish(F::DirectedEdgePredicate, v::Int, W::BitVector)::UInt
    return hash(UInt(3) * (v == F.i && W[F.j]) + UInt(5) * (v == F.j && W[F.i]))
end

function permute(pred::DirectedEdgePredicate, p::AbstractVector{Int})
    return DirectedEdgePredicate(p[pred.i], p[pred.j])
end

function countEdges(F::DirectedGraph)::Vector{Int}
    return [Int(sum(F.A))]
end

function isolatedVertices(F::DirectedGraph)::BitVector
    return vec(.!any(F.A; dims=1)) .&& vec(.!any(F.A; dims=2))
end
