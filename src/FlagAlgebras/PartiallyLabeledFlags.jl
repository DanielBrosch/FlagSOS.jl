export PartiallyLabeledFlag

"""
    PartiallyLabeledFlag{T} <: Flag where {T<:Flag}

A Flag `F` where the first `n` vertices are labeled. May have isolated vertices in the labeled part. Labeling such a Flag canonically cannot swap vertices in the labeled part, meaning the Flags 2-1-o and 1-2-o are different. If swaps there should be allowed, use a `ColoredFlag{T}` instead.
"""
struct PartiallyLabeledFlag{T} <: Flag where {T<:Flag}
    F::T
    n::Int
    function PartiallyLabeledFlag{T}(F::T, n::Int) where {T<:Flag}
        @assert size(F) >= n "More labeled vertices than vertices in the Flag."
        return new(F, n)
    end
    PartiallyLabeledFlag{T}(opts::Vararg; n::Int=0) where {T<:Flag} = new{T}(T(opts...), n)
    PartiallyLabeledFlag(F::T; n::Int=0) where {T<:Flag} = new{T}(F, n)
    PartiallyLabeledFlag{T}(F::T; n::Int=0) where {T<:Flag} = new{T}(F, n)
end

function numLabels(F::PartiallyLabeledFlag)
    return F.n
end

function numLabels(F::QuantumFlag{PartiallyLabeledFlag{T},D}) where {D,T<:Flag}
    length(F.coeff) == 0 && return 0

    return maximum(numLabels(k) for k in keys(F.coeff))
end

struct LabelPredicate <: Predicate
    i::Int
end

function predicateType(::Type{PartiallyLabeledFlag{T}}) where {T<:Flag}
    return Union{LabelPredicate,predicateType(T)}
end

function permute(
    F::PartiallyLabeledFlag{T}, p::AbstractVector{Int}
)::PartiallyLabeledFlag{T} where {T<:Flag}
    F.n > 0 && @assert 1:(F.n) == p[1:(F.n)]

    tmp = permute(F.F, p)

    return PartiallyLabeledFlag{T}(tmp, F.n)
end

function permute(pred::LabelPredicate, p::AbstractVector{Int})
    return LabelPredicate(p[pred.i])
end

function ==(A::PartiallyLabeledFlag{T}, B::PartiallyLabeledFlag{T}) where {T<:Flag}
    return A.F == B.F && A.n == B.n
end

function hash(A::PartiallyLabeledFlag{T}, h::UInt) where {T<:Flag}
    return hash(A.F, hash(A.n, hash(:PartiallyLabeledFlag, h)))
end

function Base.one(F::PartiallyLabeledFlag{T})::PartiallyLabeledFlag{T} where {T<:Flag}
    return PartiallyLabeledFlag{T}(one(F.F), 0)
end

Base.size(F::PartiallyLabeledFlag)::Int = size(F.F)

function Base.:*(F::PartiallyLabeledFlag{T}, G::PartiallyLabeledFlag{T}) where {T<:Flag}
    if F.n > G.n
        return G * F
    end
    n = size(F)
    m = size(G)

    return glue(F, G, vcat(1:(F.n), (m+1):(m+n-F.n)))
end

function subFlag(
    F::PartiallyLabeledFlag{T}, vertices::Vector{Int}
)::PartiallyLabeledFlag{T} where {T<:Flag}
    # sort to make sure labeled vertices are at the front
    if !issorted(vertices)
        sort!(vertices)
        @warn("Subflag vertices of a partially labeled Flag have been sorted!")
    end
    subF = subFlag(F.F, vertices)

    newLabeledNodes = length(intersect(1:(F.n), vertices))

    return PartiallyLabeledFlag{T}(subF, newLabeledNodes)
end

"""
    glue(F::PartiallyLabeledFlag{T}, G::PartiallyLabeledFlag{T}, p::Vector{Int})

Glues together the two partially labeled Flags `F` and `G`, after applying the permutation `p` to the vertices of `F`. `p` may be a permutation involving more than `size(F)` vertices, but should send the labeled part of `F` to the labeled part of `G`, without permuting indices there.
"""
function glue(
    F::PartiallyLabeledFlag{T}, G::PartiallyLabeledFlag{T}, p::AbstractVector{Int}
) where {T<:Flag}
    F.n > 0 &&
        @assert 1:(F.n) == p[1:(F.n)] "Labeled vertices should be glued to labeled vertices without being permuted."

    FG = glue(F.F, G.F, p)
    FG === nothing && return nothing

    if FG isa QuantumFlag
        return QuantumFlag{PartiallyLabeledFlag{T},typeof(FG).parameters[2]}(PartiallyLabeledFlag{T}(f, max(F.n, G.n)) => d for (f, d) in FG.coeff)
    end
    return PartiallyLabeledFlag{T}(FG, max(F.n, G.n))
end

function glueFinite(N, F::PartiallyLabeledFlag{T}, G::PartiallyLabeledFlag{T}, p::AbstractVector{Int}=vcat(1:(F.n), (size(G)+1):(size(G)+size(F)-F.n)); labelFlags=true) where {T<:Flag}
    return glueFinite_internal(N, F, G, p; labelFlags=labelFlags)
end

function vertexColor(F::PartiallyLabeledFlag{T}, v::Int) where {T<:Flag}
    if v <= F.n
        return v
    else
        return F.n + 1
    end
end

function isSym(F::PartiallyLabeledFlag, v1::Int, v2::Int)::Bool
    return vertexColor(F, v1) == vertexColor(F, v2) && isSym(F.F, v1, v2)
end

"""
    isolatedVertices(F::PartiallyLabeledFlag)::BitVector

Returns the isolated, and un-labeled vertices of `F`.
"""
function isolatedVertices(F::PartiallyLabeledFlag)::BitVector
    isoV = isolatedVertices(F.F)
    isoV[1:(F.n)] .= false
    return isoV
end

function distinguish(F::PartiallyLabeledFlag{T}, v::Int, W::BitVector)::UInt where {T<:Flag}
    return distinguish(F.F, v, W)
end

function distinguish(P::LabelPredicate, v::Int, W::BitVector)::UInt
    return hash(P.i == v + 2 * W[P.i])
end

function one(::Type{PartiallyLabeledFlag{T}}) where {T<:Flag}
    return PartiallyLabeledFlag{T}(one(T), 0)
end

function findUnknownPredicates(
    F::PartiallyLabeledFlag{T}, fixed::Vector{U}, predLimits::Vector
) where {T<:Flag,U<:AbstractVector{Int}}
    return vcat([[]], findUnknownPredicates(F.F, fixed, predLimits[2:end]))
end

function findUnknownGenerationPredicates(
    F::PartiallyLabeledFlag{T}, fixed::Vector{U}, predLimits::Vector
) where {T<:Flag,U<:AbstractVector{Int}}
    if length(predLimits) > 0 && predLimits[1] <= F.n
        return LabelPredicate[]
    end
    return [LabelPredicate[LabelPredicate(i) for i in F.n+1:size(F) if !(i in vcat(fixed...))]]
end

function countEdges(F::PartiallyLabeledFlag{T})::Vector where {T<:Flag}
    cP = countEdges(F.F)
    return [F.n, cP...]
end

function addPredicates(
    F::PartiallyLabeledFlag{T}, preds::Vector{U}) where {T<:Flag,U}

    labelPreds = filter(x -> x isa LabelPredicate, preds)
    otherPreds = filter(x -> !(x isa LabelPredicate), preds)

    F2s = length(otherPreds) > 0 ? addPredicates(F.F, otherPreds) : F.F
    F2s === nothing && return nothing

    if !(F2s isa Vector)
        F2s = [F2s]
    end
    res = PartiallyLabeledFlag{T}[]
    for F2 in F2s


        if length(labelPreds) == 0
            push!(res,PartiallyLabeledFlag{T}(F2, F.n))
            continue
            # return PartiallyLabeledFlag{T}(F2, F.n)
        end

        newLabels = setdiff!([p.i for p in labelPreds], 1:(F.n))

        pGoal = vcat(1:(F.n), newLabels, setdiff((F.n+1):size(F), newLabels))
        p = zeros(Int, size(F))
        for i in 1:size(F)
            p[pGoal[i]] = i
        end
        F3 = permute(F2, p)
        push!(res, PartiallyLabeledFlag{T}(F3, F.n + length(newLabels)))
        # return PartiallyLabeledFlag{T}(F3, F.n + length(newLabels))


        # if U == LabelPredicate
        #     F2 = length(preds) > 0 ? addPredicates(F.F, preds) : F.F
        #     F2 === nothing && return nothing
        #     newLabels = setdiff!([p.i for p in p], 1:(F.n))

        #     pGoal = vcat(1:(F.n), newLabels, setdiff((F.n + 1):size(F), newLabels))
        #     p = zeros(Int, size(F))
        #     for i in 1:size(F)
        #         p[pGoal[i]] = i
        #     end
        #     F3 = permute(F2, p)
        #     return PartiallyLabeledFlag{T}(F3, F.n + length(newLabels))
        # else
        #     if length(preds) > 0
        #         F2 = addPredicates(F.F, p, preds)
        #     else
        #         # @show U 
        #         # @show length(p)
        #         # @show p
        #         F2 = addPredicates(F.F, p)
        #     end
        #     F2 === nothing && return nothing

        #     return PartiallyLabeledFlag{T}(F2, F.n)
        # end
    end
    return res
end

# function addPredicates(F::PartiallyLabeledFlag{T}, p::Vector{U}, preds::Vararg{Vector{U}}) where {T<:Flag, U<:Predicate}
#     F2 = addPredicates(F.F, p, preds)
#     F2 === nothing && return nothing

#     return PartiallyLabeledFlag{T}(F2, F.n)
# end

function isVariableVertex(F::PartiallyLabeledFlag{T}, v::Int) where {T<:Flag}
    return v > F.n
end

function maxPredicateArguments(::Type{PartiallyLabeledFlag{T}}) where {T<:Flag}
    return maxPredicateArguments(T)
end

function QuantumFlag{T}(F::QuantumFlag{PartiallyLabeledFlag{T},D}) where {T<:Flag,D}
    res = QuantumFlag{T,D}()
    for (f, c) in F.coeff
        f2 = f.F
        res.coeff[f2] = get(res.coeff, f2, 0) + c
    end
    return res
end


function toInduced(F::Union{PartiallyLabeledFlag{T},QuantumFlag{PartiallyLabeledFlag{T}}}) where {T<:Flag}
    tmp = zeta(F)
    res = QuantumFlag{PartiallyLabeledFlag{InducedFlag{T}},Int}()
    for (G, c) in tmp.coeff
        res += c * PartiallyLabeledFlag{InducedFlag{T}}(InducedFlag{T}(G.F), G.n)
    end
    return res
end

function isAllowed(F::PartiallyLabeledFlag{T}, p) where {T}
    if p isa LabelPredicate
        return true
    else
        return isAllowed(F.F, p)
    end
end