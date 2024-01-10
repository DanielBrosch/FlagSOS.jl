export PartiallyColoredFlag

"""
    PartiallyColoredFlag{T} <: Flag where {T<:Flag}

A Flag `F` where (some of) the `n` vertices are colored. May have isolated vertices. Assumes vertices are ordered by color, with uncolored vertices at the end. Labeling such a Flag canonically cannot swap vertices with different colors, meaning the Flags 2-1-o and 1-2-o are different. If swaps there should be allowed, use a `ColoredFlag{T}` instead.
"""
struct PartiallyColoredFlag{T} <: Flag where {T<:Flag}
    F::T
    c::Dict{Int,Int}
    function PartiallyColoredFlag{T}(F::T, c::Dict{Int,Int}) where {T<:Flag}
        @assert size(F) >= maximum(keys(c); init = 0) "More colored vertices than vertices in the Flag."
        return new{T}(F, c)
    end
    function PartiallyColoredFlag{T}(opts::Vararg; c::Dict{Int,Int}=Dict{Int,Int}()) where {T<:Flag}
        return new{T}(T(opts...), c)
    end
    PartiallyColoredFlag(F::T; c::Dict{Int,Int}=Dict{Int,Int}()) where {T<:Flag} = new{T}(F, c)
    PartiallyColoredFlag{T}(F::T; c::Dict{Int,Int}=Dict{Int,Int}()) where {T<:Flag} = new{T}(F, c)
end

struct ColorPredicate <: Predicate
    i::Int
    c::Int
end

function predicateType(::Type{PartiallyColoredFlag{T}}) where {T<:Flag}
    return Union{ColorPredicate,predicateType(T)}
end

function permute(
    F::PartiallyColoredFlag{T}, p::AbstractVector{Int}
)::PartiallyColoredFlag{T} where {T<:Flag}
    # @show F
    # @show p
    # F.n > 0 && @assert 1:(F.n) == p[1:(F.n)]
    # for c in unique(F.c)
    #     pos = [i for i in 1:size(F) if length(F.c) >= i && F.c[i] == c]
    #     @assert Set(pos) == Set(p[pos])
    # end

    return PartiallyColoredFlag{T}(permute(F.F, p), Dict{Int,Int}(p[i] => c for (i, c) in F.c))
end

function permute(pred::ColorPredicate, p::AbstractVector{Int})
    return ColorPredicate(p[pred.i], pred.c)
end

function ==(A::PartiallyColoredFlag{T}, B::PartiallyColoredFlag{T}) where {T<:Flag}
    return A.F == B.F && A.c == B.c
end

function hash(A::PartiallyColoredFlag{T}, h::UInt) where {T<:Flag}
    return hash(A.F, hash(A.c, hash(:PartiallyColoredFlag, h)))
end

function Base.one(F::PartiallyColoredFlag{T})::PartiallyColoredFlag{T} where {T<:Flag}
    return PartiallyColoredFlag{T}(one(F.F))
end

Base.size(F::PartiallyColoredFlag)::Int = size(F.F)

function Base.:*(F::PartiallyColoredFlag{T}, G::PartiallyColoredFlag{T}) where {T<:Flag}
    @assert F.c == G.c
    @assert Set(collect(keys(F.c))) == Set(1:length(F.c))

    n = size(F)
    m = size(G)

    return glue(F, G, vcat(1:length(F.c), (m+1):(m+n-length(F.c))))
end

function subFlag(
    F::PartiallyColoredFlag{T}, vertices::Vector{Int}
)::PartiallyColoredFlag{T} where {T<:Flag}
    # sort to make sure labeled vertices are at the front
    if !issorted(vertices)
        sort!(vertices)
        @warn("Subflag vertices of a partially colored Flag have been sorted!")
    end
    subF = subFlag(F.F, vertices)

    # newLabeledNodes = length(intersect(1:(F.n), vertices))

    # newColors = Int[F.c[i] for i in vertices if i <= length(F.c)]
    newColors = Dict{Int,Int}(findfirst(x->x==i, vertices) => c for (i, c) in F.c if i in vertices)

    return PartiallyColoredFlag{T}(subF, newColors)
end

"""
    glue(F::PartiallyColoredFlag{T}, G::PartiallyColoredFlag{T}, p::Vector{Int})

Glues together the two partially labeled Flags `F` and `G`, after applying the permutation `p` to the vertices of `F`. `p` may be a permutation involving more than `size(F)` vertices, but should vertices with the same colors to vertices with the same colors.
"""
function glue(
    F::PartiallyColoredFlag{T}, G::PartiallyColoredFlag{T}, p::AbstractVector{Int}
) where {T<:Flag}
    # F.n > 0 &&
    # @assert 1:(F.n) == p[1:(F.n)] "Labeled vertices should be glued to labeled vertices without being permuted."

    # @show F
    # @show G
    # @show p

    # @assert F.c[p[1:length(F.c)]] == G.c
    @assert F.c == G.c
    @assert p[collect(keys(F.c))] == collect(keys(F.c))

    FG = glue(F.F, G.F, p)
    FG === nothing && return nothing

    if FG isa QuantumFlag
        return QuantumFlag(PartiallyColoredFlag{T}(f, G.c) => d for (f, d) in FG.coeff)
    end
    return PartiallyColoredFlag{T}(FG, G.c)
end

function glueFinite(
    N,
    F::PartiallyColoredFlag{T},
    G::PartiallyColoredFlag{T},
    p::AbstractVector{Int}=vcat(1:length(F.c), (size(G)+1):(size(G)+size(F)-length(F.c)));
    labelFlags=true,
) where {T<:Flag}
    return glueFinite_internal(N, F, G, p; labelFlags=labelFlags)
end

function vertexColor(F::PartiallyColoredFlag{T}, v::Int) where {T<:Flag}
    if haskey(F.c, v)
        cTmp = F.c[v]
        for i = 1:cTmp - 1
            if !(i in values(F.c))
                cTmp = cTmp - 1
            end
        end
        return cTmp
        # return findfirst(x -> x == F.c[v], sort(unique(values(F.c))))
    else
        return length(unique(values(F.c))) + 1
    end
end

function isSym(F::PartiallyColoredFlag, v1::Int, v2::Int)::Bool
    return vertexColor(F, v1) == vertexColor(F, v2) && isSym(F.F, v1, v2)
end

"""
    isolatedVertices(F::PartiallyColoredFlag)::BitVector

Returns the isolated, and un-labeled vertices of `F`.
"""
function isolatedVertices(F::PartiallyColoredFlag)::BitVector
    isoV = isolatedVertices(F.F)
    isoV[collect(keys(F.c))] .= false
    return isoV
end

function distinguish(F::PartiallyColoredFlag{T}, v::Int, W::BitVector)::UInt where {T<:Flag}
    return distinguish(F.F, v, W)
end

function distinguish(P::ColorPredicate, v::Int, W::BitVector)::UInt
    return hash(P.i == v + 2 * W[P.i], hash(P.c))
end

function one(::Type{PartiallyColoredFlag{T}}) where {T<:Flag}
    return PartiallyColoredFlag{T}(one(T))
end

function findUnknownPredicates(
    F::PartiallyColoredFlag{T}, fixed::Vector{U}, predLimits::Vector
) where {T<:Flag,U<:AbstractVector{Int}}
    return vcat([[]], findUnknownPredicates(F.F, fixed, predLimits[2:end]))
end

function findUnknownGenerationPredicates(
    F::PartiallyColoredFlag{T}, fixed::Vector{U}, predLimits::Vector
) where {T<:Flag,U<:AbstractVector{Int}}
    # if length(predLimits) > 0 && predLimits[1] <= F.n
    #     return ColorPredicate[]
    # end

    res = ColorPredicate[]
    for c in 1:length(predLimits[1])
        if count(x->x==c, values(F.c)) < predLimits[1][c]
            for i = 1:size(F)
                if !(i in fixed) && !haskey(F.c, i)
                    push!(res, ColorPredicate(i, c))
                end
            end
        end
    end

    # return [
    #     ColorPredicate[
    #         ColorPredicate(i, c) for i in (length(F.c)+1):size(F) for c in 1:length(predLimits[1]) if !(i in vcat(fixed...) && count(x -> x == c, F.c) < predLimits[1][c])
    #     ],
    # ]
    return [res]
end

function countEdges(F::PartiallyColoredFlag{T}) where {T<:Flag}
    cP = countEdges(F.F)
    return [[count(x -> x == c, values(F.c)) for c = 1:maximum(values(F.c); init=0)], cP...]
end

function addPredicates(F::PartiallyColoredFlag{T}, p::Vector{U}) where {T<:Flag,U}
    colorPreds = filter(x -> x isa ColorPredicate, p)
    otherPreds = filter(x -> !(x isa ColorPredicate), p)

    F2 = length(otherPreds) > 0 ? addPredicates(F.F, otherPreds) : F.F
    F2 === nothing && return nothing

    if length(colorPreds) == 0
        return PartiallyColoredFlag{T}(F2, F.c)
    end
    
    newC = deepcopy(F.c)
    for pred in colorPreds 
        if haskey(newC, pred.i) && newC[pred.i] != pred.c 
            return nothing 
        end
        newC[pred.i] = pred.c
    end
    
    return PartiallyColoredFlag{T}(F2, newC)

    # pGoal = collect(1:size(F))
    # cGoal = deepcopy(F.c)

    # sort!(colorPreds; by=x -> x.i)

    # for pred in colorPreds
    #     if pred.i <= length(cGoal)
    #         if pred.c != cGoal[pred.i]
    #             return nothing
    #         end
    #         continue
    #     end
    #     insertPos = findfirst(x -> x > pred.c, cGoal)
    #     if insertPos === nothing
    #         push!(cGoal, pred.c)
    #         pGoal[pred.i] = length(cGoal)
    #         pGoal[length(cGoal):pred.i-1] .= pGoal[length(cGoal):pred.i-1] .+ 1
    #     else
    #         push!(cGoal, 0)
    #         cGoal[insertPos+1:end] .= cGoal[insertPos:end-1]
    #         cGoal[insertPos] = pred.c
    #         pGoal[pred.i] = insertPos
    #         pGoal[insertPos:pred.i-1] .= pGoal[insertPos:pred.i-1] .+ 1
    #     end
    # end

    # # newLabels = setdiff!([p.i for p in p], 1:length(F.c))

    # # pGoal = vcat(1:(F.n), newLabels, setdiff((F.n + 1):size(F), newLabels))
    # # p = zeros(Int, size(F))
    # # for i in 1:size(F)
    # #     p[pGoal[i]] = i
    # # end
    # F3 = permute(F2, pGoal)
    # return PartiallyColoredFlag{T}(F3, cGoal)

end

function isVariableVertex(F::PartiallyColoredFlag{T}, v::Int) where {T<:Flag}
    return !(v in keys(F.c))
end

function maxPredicateArguments(::Type{PartiallyColoredFlag{T}}) where {T<:Flag}
    return maxPredicateArguments(T)
end

function QuantumFlag{T}(F::QuantumFlag{PartiallyColoredFlag{T},D}) where {T<:Flag,D}
    res = QuantumFlag{T,D}()
    for (f, c) in F.coeff
        f2 = f.F
        res.coeff[f2] = get(res.coeff, f2, 0) + c
    end
    return res
end

function isAllowed(F::PartiallyColoredFlag{T}, p) where {T}
    if p isa ColorPredicate
        return !haskey(F.c, p.i) || F.c[p.i] == p.c
        # return p.i > length(F.c) || p.c == F.c[p.i]
    else
        return isAllowed(F.F, p)
    end
end