export ConstantWeightCode, Hypergraph

using LinearAlgebra
using Combinatorics

# W == weight of edges in uniform ConstantWeightCode 
# If W == 0, then all weights are allowed
# D == minimum hamming distance between edges
struct ConstantWeightCode{W,D} <: Flag
    A::BitMatrix
    function ConstantWeightCode{W,D}(A::Matrix{Bool}) where {W,D}
        return ConstantWeightCode{W,D}(BitMatrix(A))
    end
    ConstantWeightCode{W,D}(A::BitMatrix) where {W,D} = begin
        A = sortslices(A; dims=1)
        new{W,D}(A)
    end
    ConstantWeightCode{W,D}() where {W,D} = new{W,D}(BitMatrix(undef, 0, 0))
end

const Hypergraph{W} = ConstantWeightCode{W,0}

function ==(A::ConstantWeightCode, B::ConstantWeightCode)
    return A.A == B.A
end
function hash(A::ConstantWeightCode, h::UInt)
    return hash(A.A, hash(:ConstantWeightCode, h))
end

Base.one(::Type{ConstantWeightCode{W}}) where {W} = ConstantWeightCode{W}()
Base.one(::Type{ConstantWeightCode{W,D}}) where {W,D} = ConstantWeightCode{W,D}()

function size(G::ConstantWeightCode)::Int
    return size(G.A, 2) #number of columns of incidence matrix = nr of vertices
end

struct HyperEdgePredicate <: Predicate
    e::Set{Int}
    HyperEdgePredicate(e::Set{Int}) = new(e)
    HyperEdgePredicate(e::AbstractVector{Int}) = new(Set(e))
end

function predicateType(::Type{ConstantWeightCode{W,D}}) where {W,D}
    return HyperEdgePredicate
end

function ==(A::HyperEdgePredicate, B::HyperEdgePredicate)
    return A.e == B.e
end
function hash(P::HyperEdgePredicate, h::UInt)
    return hash(P.e, hash(:HyperEdgePredicate, h))
end
function permute(pred::HyperEdgePredicate, p::AbstractVector{Int})
    return HyperEdgePredicate(p[collect(pred.e)])
end

function isAllowed(F::ConstantWeightCode{W,D}, P::HyperEdgePredicate) where {W,D}
    maxOverlap = min(W - 1, Int(W - D / 2))
    return !any(sum(F.A[:, collect(P.e)]; dims=2) .> maxOverlap)
end

#TODO: implement for arbitrary weight (W = 0)
function findUnknownPredicates(
    F::ConstantWeightCode{W,D}, fixed::Vector{U}, predLimits::Vector
)::Vector{Vector{HyperEdgePredicate}} where {W,D,U<:AbstractVector{Int}}
    res = HyperEdgePredicate[]

    maxOverlap = min(W - 1, Int(W - D / 2))

    for e in combinations(1:size(F), W)
        if !any([sum(F.A[i, :][e]) > maxOverlap for i in 1:size(F.A, 1)]) && !any(issubset(e, f) for f in fixed)
            push!(res, HyperEdgePredicate(Set(e)))
        end
    end
    return [res]
end

function isAllowed(G::ConstantWeightCode{W,D}) where {W,D}
    if D == 0 || size(G) == 0
        return true
    end
    maxOverlap = Int(W - D / 2)
    tmp = G.A * G.A'
    tmp[diagind(tmp)] .= 0
    return maximum(tmp; init=0) <= maxOverlap
end

function isSym(g::ConstantWeightCode{W,D}, v1::Int, v2::Int)::Bool where {W,D}
    # n = size(g)
    return g.A[:, v1] == g.A[:, v2]
end

function addPredicates(
    G::ConstantWeightCode{W,D}, preds::Vector{HyperEdgePredicate}
) where {W,D}
    A = Matrix(copy(G.A))

    for edge in preds
        @assert W == 0 || length(edge.e) == W "Edge weight doesn't match ConstantWeightCode"
        edgevec = BitMatrix(undef, 1, size(A, 2))
        edgevec[collect(edge.e)] .= 1
        #check if G DOES NOT CONTAIN edge:
        if !any(edgevec == A[i, :] for i in 1:size(A, 1))
            A = [A; edgevec]
        end
    end
    res = ConstantWeightCode{W,D}(A)
    !isAllowed(res) && return nothing
    return res
end

function glue(
    g1::ConstantWeightCode{W,D}, g2::ConstantWeightCode{W,D}, p::AbstractVector{Int}
) where {W,D}
    n1 = size(g1)
    n2 = size(g2)
    # n = max(n2, length(p) > 0 && n1 > 0 ? maximum(p[1:n1]) : 0)
    n = max(n2, length(p) > 0 ? maximum(p) : 0)

    permutedG1 = BitMatrix(zeros(size(g1.A, 1), n))
    permutedG1[:, p[1:n1]] .|= g1.A

    extendedG2 = BitMatrix(zeros(size(g2.A, 1), n))
    extendedG2[:, 1:n2] .|= g2.A

    newG = [permutedG1; extendedG2]

    #remove duplicate rows:
    newG = unique(newG; dims=1)
    #remove zero rows:
    if size(newG, 1) != 0
        newG = newG[vec(mapslices(col -> any(col .!= 0), newG; dims=2)), :]
    end

    res = ConstantWeightCode{W,D}(newG)

    if !isAllowed(res)
        return nothing
    end
    return res
end

function maxPredicateArguments(::Type{ConstantWeightCode{W,D}}) where {W,D}
    W == 0 && return Inf
    return W
end

# TODO: W = 0: Delete all edges where at least one vertex gets deleted
function subFlag(
    F::ConstantWeightCode{W,D}, vertices::AbstractVector{Int}
)::ConstantWeightCode{W,D} where {W,D}
    @assert W != 0 "TODO"

    newA = F.A[:, vertices]

    if size(newA, 1) != 0
        newA = newA[vec(mapslices(col -> sum(col) == W, newA; dims=2)), :]
    end
    return ConstantWeightCode{W,D}(newA)
end

function distinguish(F::ConstantWeightCode, v::Int, W::BitVector)::UInt
    @views subA = F.A[F.A[:, v] .== 1, W]
    rowSums = vec(sum(subA; dims=2))
    return hash(sort!(rowSums))
end

function distinguish(F::HyperEdgePredicate, v::Int, W::BitVector)::UInt
    if !(v in F.e)
        return 0
    end
    return hash(sum(W[i] for i in F.e))
end

function countEdges(F::ConstantWeightCode)::Vector{Int}
    size(F.A, 1) == 0 && return [0]

    return [sum(mapslices(col -> any(col .!= 0), F.A; dims=2))]
end

function isolatedVertices(F::ConstantWeightCode)::BitVector
    return vec(.!any(F.A; dims=1))
end
