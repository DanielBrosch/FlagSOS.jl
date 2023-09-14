export DirectedGraph

# TODO: Permuting vertices changes direction of edges!

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

isValid(A::DirectedGraph{true}) = true
isValid(A::DirectedGraph{false}) = !any(A.A .&& A.A')

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

function findUnknownPredicates(
    F::DirectedGraph{allowDigons}, fixed::Vector{U}
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
    A = Matrix(copy(G.A))
    for p in preds
        allowDigons == false && A[p.j, p.i] == 1 && return nothing
        A[p.i, p.j] = 1
    end
    return DirectedGraph(A)
end

# apply p to g1, then glue together
function glue(g1::DirectedGraph, g2::DirectedGraph, p::AbstractVector{Int})
    n1 = size(g1)
    n2 = size(g2)
    n = max(n2, length(p) > 0 ? maximum(p) : 0)

    res = BitMatrix(zeros(n, n))
    res[1:n2, 1:n2] = g2.A
    res[p[1:n1], p[1:n1]] .|= g1.A

    res = DirectedGraph(res)
    !isValid(res) && return nothing
    return res
end

function glue(Gs::Vararg{DirectedGraph})
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

    res = DirectedGraph(res)
    !isValid(res) && return nothing
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

function distinguish(F::DirectedGraph, v::Int, W::BitVector)
    return (sum(F.A[W, v]), sum(F.A[v, W]))
end

function distinguish(F::DirectedEdgePredicate, v::Int, W::BitVector)
    return 3 * (v == F.i && W[F.j]) + 5 * (v == F.j && W[F.i])
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
