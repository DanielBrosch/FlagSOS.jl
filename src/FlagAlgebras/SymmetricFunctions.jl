export SymmetricFunction

struct SymmetricFunction <: Flag
    exponents::Dict{Int,Int}

    SymmetricFunction() = new(Dict{Int,Int}())
    SymmetricFunction(exponents::Dict{Int,Int}) = new(exponents)
    SymmetricFunction(ps::Pair{Int,Int}...) = new(Dict{Int,Int}(ps))
    SymmetricFunction(v::Vector{Int}) = new(Dict{Int,Int}(i => v[i] for i in eachindex(v)))
    SymmetricFunction(iterable) = new(Dict{Int,Int}(iterable))
end

function Base.show(io::IO, T::SymmetricFunction)
    print(io, "m_norm(")
    for i in 1:size(T)
        print(io, get(T.exponents, i, 0))
        i < size(T) && print(io, ",")
    end
    print(io, ")")
end

function ==(A::SymmetricFunction, B::SymmetricFunction)
    return A.exponents == B.exponents
end

function hash(A::SymmetricFunction, h::UInt)
    return hash(A.exponents, hash(:SymmetricFunction, h))
end

function Base.one(::Type{SymmetricFunction})::SymmetricFunction
    return SymmetricFunction()
end

function Base.one(::SymmetricFunction)::SymmetricFunction
    return SymmetricFunction()
end

Base.size(F::SymmetricFunction)::Int = maximum(keys(F.exponents); init=0)

function labelCanonically(F::SymmetricFunction)::SymmetricFunction
    tmp = sort!(filter(x -> x != 0, collect(values(F.exponents))); rev=true)
    return SymmetricFunction(i => tmp[i] for i in eachindex(tmp))
end

function countEdges(F::SymmetricFunction)::Vector{Int}
    return [sum(values(F.exponents))]
end

function maxPredicateArguments(::Type{SymmetricFunction})
    return 1
end

function subFlag(F::SymmetricFunction, vertices::Vector{Int})::SymmetricFunction
    # @show vertices

    newExp = Dict{Int, Int}()
    for (i, v) in enumerate(vertices)
        newExp[i] = get(F.exponents, v, 0)
    end

    return SymmetricFunction(newExp)
end

function glue(
    F::SymmetricFunction, G::SymmetricFunction, p::AbstractVector{Int}
)
    res = deepcopy(G.exponents)
    for (i, c) in F.exponents
        res[p[i]] = get(res, p[i], 0) + c
    end
    for i = 1:maximum(p; init = 0)
        res[i] = get(res, i, 0)
    end
    return SymmetricFunction(res)
end

function distinguish(F::SymmetricFunction, v::Int, W::BitVector)::UInt
    return hash(get(F.exponents, v, 0))
end

function isolatedVertices(F::SymmetricFunction)::BitVector
    return [get(F.exponents,i,0) == 0 for i=1:size(F)]
end

function predicateType(::Type{SymmetricFunction})
    return LabelPredicate
end

function addPredicates(F::SymmetricFunction, preds::Vector{LabelPredicate})
    res = deepcopy(F)
    for P in preds
        res.exponents[P.i] = get(res.exponents, P.i, 0) + 1
    end
    return res
end

function permute(F::SymmetricFunction, p::AbstractVector{Int})
    res = SymmetricFunction(p[i] => c for (i, c) in F.exponents)
    for i = 1:maximum(p)
        res.exponents[i] = get(res.exponents, i, 0)
    end
    return res
end

function findUnknownPredicates(
    F::SymmetricFunction, fixed::Vector{U}, predLimits::Vector
) where {U<:AbstractVector{Int}}
    return [[LabelPredicate(i) for i in 1:size(F) if !any((i in part) for part in fixed)]]
end

# function findUnknownGenerationPredicates(
#     F::SymmetricFunction, fixed::Vector{U}, predLimits::Vector
# ) where {U<:AbstractVector{Int}}
#     return findUnknownPredicates(F, fixed, predLimits)
# end

function isSym(F::SymmetricFunction, v1::Int, v2::Int)::Bool
    return get(F.exponents, v1, 0) == get(F.exponents, v2, 0)
end

function allowMultiEdges(::Type{SymmetricFunction})
    return true
end

# function generateAll(
#     ::Type{SymmetricFunction{F}}, maxVertices::Int, maxPredicates::Vector{Int}
# ) where {F<:Flag}
#     tmp = generateAll(F, maxVertices, maxPredicates)
#     return [SymmetricFunction{F}(f) for f in tmp]
# end

# function eliminateIsolated(F::SymmetricFunction)
#     return SymmetricFunction(filter(x -> x.second != 0, F.exponents))
# end