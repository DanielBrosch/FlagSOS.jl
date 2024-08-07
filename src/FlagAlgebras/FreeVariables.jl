# Sometimes one may want to add free variables to the model, for example to model sqrt(edge density). To make this possible, we model them as a "fake flag algebra", with only finite sized models and no S_infty symmetries

export FreeVariable, FreeVariables

struct FreeVariable <: Flag
    exponent::Int
    FreeVariable() = new(0)
    FreeVariable(exponent::Int) = new(exponent)
end

FreeVariables{N} = ProductFlag{NTuple{N,FreeVariable}}

struct IncreaseDegreePredicate <: Predicate
end

function permute(pred::IncreaseDegreePredicate, p::AbstractVector{Int})
    return pred
end

function Base.show(io::IO, T::FreeVariable)
    return print(io, "x^$(T.exponent)")
end

function ==(A::FreeVariable, B::FreeVariable)
    return A.exponent == B.exponent
end

function hash(A::FreeVariable, h::UInt)
    return hash(A.exponent, hash(:FreeVariable, h))
end

function distinguish(P::IncreaseDegreePredicate, v::Int, W::BitVector)::UInt
    return UInt(1)
end


Base.one(::Type{FreeVariable})::FreeVariable = FreeVariable()

Base.one(::FreeVariable)::FreeVariable = FreeVariable()

Base.size(F::FreeVariable)::Int = 0

function labelCanonically(F::FreeVariable)::FreeVariable
    return F
end

function countEdges(F::FreeVariable)::Vector{Int}
    return [F.exponent]
end

function maxPredicateArguments(::Type{FreeVariable})
    return 1
end

function subFlag(F::FreeVariable, vertices::Vector{Int})::FreeVariable
    return F
end

function glue(F::FreeVariable, G::FreeVariable, p::AbstractVector{Int})
    return FreeVariable(F.exponent + G.exponent)
end

function distinguish(F::FreeVariable, v::Int, W::BitVector)::UInt
    return UInt(1)
end

function isolatedVertices(F::FreeVariable)::BitVector
    return [true;]
end

function predicateType(::Type{FreeVariable})
    return IncreaseDegreePredicate
end

function addPredicates(F::FreeVariable, preds::Vector{IncreaseDegreePredicate})
    return FreeVariable(F.exponent + length(preds))
end

function permute(F::FreeVariable, p::AbstractVector{Int})
    return F
end

function findUnknownPredicates(
    F::FreeVariable, fixed::Vector{U}, predLimits::Vector
) where {U<:AbstractVector{Int}}
    if any(1 in f for f in fixed)
        return [IncreaseDegreePredicate[]]
    end
    return [IncreaseDegreePredicate[IncreaseDegreePredicate()]]
end

function findUnknownGenerationPredicates(
    F::FreeVariable, fixed::Vector{U}, predLimits::Vector
) where {U<:AbstractVector{Int}}
    return findUnknownPredicates(F, fixed, predLimits)
end

function isSym(F::FreeVariable, v1::Int, v2::Int)::Bool
    return v1 == v2
end

function allowMultiEdges(::Type{FreeVariable})
    return true
end

# function generateAll(
#     ::Type{FreeVariable{F}}, maxVertices::Int, maxPredicates::Vector{Int}
# ) where {F<:Flag}
#     tmp = generateAll(F, maxVertices, maxPredicates)
#     return [FreeVariable{F}(f) for f in tmp]
# end

# function eliminateIsolated(F::FreeVariable)
#     return FreeVariable(filter(x -> x.second != 0, F.exponent))
# end