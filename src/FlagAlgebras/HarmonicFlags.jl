export HarmonicFlag

"""
    HarmonicFlag{T} <: Flag where {T <: Flag}

Turns a given Flag into its harmonic equivalent. E.g. `HarmonicFlag{Graph}(P2)`, where `P2 = Graph(Bool[0 0 1; 0 0 1; 1 1 0])` is the path on three vertices, describes the Flag corresponding to the harmonic path density. Only makes sense if there is an equivalent to "edges" in the Flag type `T`.
"""
struct HarmonicFlag{T} <: Flag where {T<:Flag}
    F::T
    function HarmonicFlag{T}(F::T) where {T<:Flag}
        new{T}(F)
    end
    function HarmonicFlag{T}(opts...) where {T<:Flag}
        new(T(opts...))
    end
    HarmonicFlag{T}(::Nothing) where {T<:Flag} = nothing
end

function ==(A::HarmonicFlag{T}, B::HarmonicFlag{T}) where {T<:Flag}
    return A.F == B.F
end
function hash(A::HarmonicFlag{T}, h::UInt) where {T<:Flag}
    return hash(A.F, hash(:HarmonicFlag, h))
end

function Base.one(::Type{HarmonicFlag{T}})::HarmonicFlag{T} where {T<:Flag}
    return HarmonicFlag{T}(one(T))
end

function Base.one(F::HarmonicFlag{T})::HarmonicFlag{T} where {T<:Flag}
    return HarmonicFlag{T}(one(F.F))
end

Base.size(F::HarmonicFlag)::Int = size(F.F)

function labelCanonically(F::HarmonicFlag{T})::HarmonicFlag{T} where {T<:Flag}
    return HarmonicFlag{T}(label(F.F; removeIsolated=true)[1])
end

function countEdges(F::HarmonicFlag{T})::Vector{Int} where {T<:Flag}
    return countEdges(F.F)
end

function maxPredicateArguments(::Type{HarmonicFlag{T}}) where {T<:Flag}
    return maxPredicateArguments(T)
end

function predicateType(::Type{HarmonicFlag{T}}) where {T<:Flag}
    return predicateType(T)
end

function subFlag(F::HarmonicFlag{T}, vertices::Vector{Int})::HarmonicFlag{T} where {T<:Flag}
    return HarmonicFlag{T}(subFlag(F.F, vertices))
end

"""
    glue(F::HarmonicFlag{T}, G::HarmonicFlag{T}, p::Vector{Int})

Glues together the two harmonic Flags `F` and `G`, after applying the permutation `p` to the vertices of `F`. `p` may be a permutation involving more than `size(F)` vertices. Since these Flags describe harmonic densities, the result is another flag of type `F`, where double edges cancelled out.
"""
function glue(
    F::HarmonicFlag{T}, G::HarmonicFlag{T}, p::AbstractVector{Int}
)::HarmonicFlag{T} where {T<:Flag}
    @error "TODO: Generic harmonic flags based on predicates"
end

function distinguish(F::HarmonicFlag{T}, v::Int, W::BitVector)::UInt where {T<:Flag}
    return distinguish(F.F, v, W)
end

function isolatedVertices(F::HarmonicFlag{T})::BitVector where {T<:Flag}
    return isolatedVertices(F.F)
end

function addPredicates(
    F::HarmonicFlag{T}, preds::Vector{U}
) where {T<:Flag,U<:Predicate}
    tmp = addPredicates(F.F, preds)
    if tmp === nothing
        return nothing
    end
    return HarmonicFlag{T}(tmp)
end

function permute(F::HarmonicFlag{T}, p::HarmonicFlag{Int}) where {T<:Flag}
    return HarmonicFlag{T}(glue(F.F, one(T), p))
end

function findUnknownPredicates(
    F::HarmonicFlag{T}, fixed::Vector{U},predLimits::Vector
) where {T<:Flag,U<:AbstractVector{Int}}
    return findUnknownPredicates(F.F, fixed, predLimits)
end

function isSym(F::HarmonicFlag, v1::Int, v2::Int)::Bool
    return isSym(F.F, v1, v2)
end

function generateAll(
    ::Type{HarmonicFlag{F}}, maxVertices::Int, maxPredicates::Vector{Int}
) where {F<:Flag}
    tmp = generateAll(F, maxVertices, maxPredicates)
    return [HarmonicFlag{F}(f) for f in tmp]
end

function glue(g1::HarmonicFlag{Graph}, g2::HarmonicFlag{Graph}, p::AbstractVector{Int})::HarmonicFlag{Graph}
    n1 = size(g1)
    n2 = size(g2)
    n = max(n2, length(p) > 0 ? maximum(p) : 0)

    res = BitMatrix(zeros(n, n))
    res[1:n2, 1:n2] = g2.F.A

    # Character Flags
    res[p[1:n1], p[1:n1]] .⊻= g1.F.A
    # nZs = vec(sum(res, dims=1) .> 0)
    # res = res[nZs, nZs]

    return HarmonicFlag{Graph}(Symmetric(res))
end

function glue(Gs::Vararg{HarmonicFlag{Graph}})::HarmonicFlag{Graph}
    if length(Gs) == 1
        return Gs[1]
    elseif length(Gs) == 2
        return glue(Gs..., 1:size(Gs[1]))
    end

    n = size(Gs[1])
    res::BitMatrix = BitMatrix(zeros(n, n))

    for g in Gs
        # Character Flags
        res .⊻= g.F.A
    end
    # nZs = vec(sum(res, dims=1) .> 0)
    # res = res[nZs, nZs]

    return HarmonicFlag{Graph}(Symmetric(res))
end