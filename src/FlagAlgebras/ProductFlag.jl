# Multiple models on the same vertices. E.g. G = (V, E1, E2) double graph. Permutations = Double ordering. Symmetric functions in R3 = triple symmetric functions 
# Corresponds to the product of the models, see 4.1 https://plato.stanford.edu/Archives/sum2005/entries/modeltheory-fo/#:~:text=First%2Dorder%20model%20theory%2C%20also,structures%20that%20satisfy%20these%20descriptions.


export ProductFlag



struct ProductFlag{FT} <: Flag where {FT<:Tuple{Vararg{Flag}}}
    Fs::FT

    ProductFlag{FT}(Fs::FT) where {FT} = new{FT}(Fs)
    ProductFlag{FT}() where {FT} = new{FT}(Tuple(F() for F in fieldtypes(FT)))
end

function Base.show(io::IO, F::ProductFlag)
    print(io, "(")
    first = true
    for f in F.Fs
        if !first
            print(io, ",")
        end
        print(io, f)
        first = false 
    end
    print(io, ")")
end

import Base.==
function ==(A::ProductFlag{FT}, B::ProductFlag{FT}) where {FT}
    return all(A.Fs[i] == B.Fs[i] for i = 1:length(A.Fs))
end
import Base.hash
function hash(A::ProductFlag{FT}, h::UInt) where {FT}
    return hash(A.Fs, hash(:ProductFlag, hash(FT, h)))
end

function isAllowed(A::ProductFlag)
    if !all(x -> isAllowed(x), A.Fs)
        return false
    end

    return all(length(unique([vertexColor(f, i) for f in A.Fs])) == 1 for i = 1:size(A))
end


function Base.one(::Type{ProductFlag{FT}}) where {FT}
    return ProductFlag{FT}()
end

function size(G::ProductFlag)::Int
    return maximum([size(F) for F in G.Fs])
end

function isAllowed(F::ProductFlag{FT}, p::Tuple{Int,P}) where {FT,P<:Predicate}
    return isAllowed(F.Fs[p[1]], p[2])
end

function predicateType(::Type{ProductFlag{FT}}) where {FT}
    return Tuple{Int,Union{[predicateType(F) for F in fieldtypes(FT)]...}}
end

function findUnknownPredicates(
    F::ProductFlag{FT}, fixed::Vector{U}, predLimits::Vector
)::Vector{Vector{Tuple{Int,Predicate}}} where {U<:AbstractVector{Int},FT}
    res = Vector{predicateType(ProductFlag{FT})}[]
    for (i, Ft) in enumerate(fieldtypes(FT))
        tmp = predicateType(ProductFlag{FT})[]
        # if length(predLimits) == length(fieldtypes(FT)) && sum(countEdges(F.Fs[i])) >= predLimits[i]
        #     push!(res, tmp)
        #     continue
        # end

        if length(predLimits) == length(fieldtypes(FT))
            FIP = findUnknownPredicates(F.Fs[i], fixed, predLimits[i])
        else
            FIP = findUnknownPredicates(F.Fs[i], fixed, [predLimits[1]])
        end

        # @assert length(FIP) == 1
        for fips in FIP
            for p in fips
                push!(tmp, (i, p))
            end
        end
        push!(res, tmp)
    end
    return res
end

function findUnknownGenerationPredicates(
    F::ProductFlag{FT}, fixed::Vector{U}, predLimits::Vector
)::Vector{Vector{Tuple{Int,Predicate}}} where {U<:AbstractVector{Int},FT}
    res = Vector{predicateType(ProductFlag{FT})}[]
    for (i, Ft) in enumerate(fieldtypes(FT))
        tmp = predicateType(ProductFlag{FT})[]
        # if length(predLimits) == length(fieldtypes(FT)) && sum(countEdges(F.Fs[i])) >= predLimits[i]
        #     push!(res, tmp)
        #     continue
        # end
        if length(predLimits) == length(fieldtypes(FT))
            FIP = findUnknownGenerationPredicates(F.Fs[i], fixed, predLimits[i])
        else
            FIP = findUnknownGenerationPredicates(F.Fs[i], fixed, [predLimits[1]])
        end
        # FIP = findUnknownGenerationPredicates(F.Fs[i], fixed, predLimits[i])
        # @assert length(FIP) == 1
        for fips in FIP
            for p in fips
                push!(tmp, (i, p))
            end
        end
        push!(res, tmp)
    end
    return res
end

function addPredicates(
    G::ProductFlag{FT}, preds::Vector{Tuple{Int,P}}) where {FT,P}
    tmp = []
    for (i, F) in enumerate(G.Fs)
        newF = addPredicates(F, predicateType(typeof(F))[p[2] for p in preds if p[1] == i])
        push!(tmp, newF)
    end

    res = ProductFlag{FT}(Tuple(tmp))
    # @show countEdges(G)
    # @show countEdges(res)
    # @assert sum(countEdges(G)) < sum(countEdges(res))
    return res
end

# apply p to g1, then glue together
function glue(
    g1::ProductFlag{FT}, g2::ProductFlag{FT}, p::AbstractVector{Int}
) where {FT}
    return ProductFlag{FT}(Tuple(glue(g1.Fs[i], g2.Fs[i], p) for i = 1:length(fieldtypes(FT))))
end

# check if swapping v1 and v2 leaves g invariant
function isSym(g::ProductFlag, v1::Int, v2::Int)::Bool
    return all(x -> isSym(x, v1, v2), g.Fs)
end

function subFlag(F::ProductFlag{FT}, vertices::AbstractVector{Int})::ProductFlag{FT} where {FT}
    return ProductFlag{FT}(Tuple(subFlag(f, vertices) for f in F.Fs))
end

function maxPredicateArguments(::Type{ProductFlag{FT}}) where {FT}
    return maximum(maxPredicateArguments, fieldtypes(FT))
end

function distinguish(F::ProductFlag{FT}, v::Int, W::BitVector)::UInt where {FT}
    res = hash(FT)
    for f in F.Fs
        res = hash(distinguish(f, v, W), res)
    end
    return res
end

function distinguish(pred::Tuple{Int,P}, v::Int, W::BitVector)::UInt where {P<:Predicate}
    return distinguish(pred[2], v, W)
end

function permute(pred::Tuple{Int,P}, p::AbstractVector{Int}) where {P<:Predicate}
    return tuple(pred[1], permute(pred[2], p))
end

function permute(
    F::ProductFlag{FT}, p::AbstractVector{Int}
) where {FT}
    pF = [permute(f, p) for f in F.Fs]
    if any(x -> x === nothing, pF)
        return nothing
    end
    return ProductFlag{FT}(Tuple(pF))
end

function countEdges(F::ProductFlag)
    return [countEdges(f) for f in F.Fs]
end

function isolatedVertices(F::ProductFlag{FT})::BitVector where {FT}
    tmp = BitVector(ones(Bool, size(F)))
    for f in F.Fs
        # @show tmp 
        # @show size(f)
        # @show isolatedVertices(f)
        tmp[1:size(f)] .= tmp[1:size(f)] .&& isolatedVertices(f)
    end
    return tmp
end

function allowMultiEdges(::Type{ProductFlag{FT}}) where {FT}
    return any(allowMultiEdges, fieldtypes(FT))
end

function vertexColor(F::ProductFlag{FT}, v::Int) where {FT}
    # colorCombinations = sort!(unique([[vertexColor(f, i) for f in F.Fs] for i = 1:size(F)]))

    cs = hash(Int[vertexColor(f, v) for f in F.Fs])
    colorCombinations = UInt[cs]
    # colorCombinations = Vector{Int}[cs]

    for i = 1:size(F)
        if i != v
            ct = hash(Int[vertexColor(f, i) for f in F.Fs])
            if !(ct in colorCombinations)
                push!(colorCombinations, ct)
            end
        end
    end
    sort!(colorCombinations)


    return findfirst(x -> x == cs, colorCombinations)

    # @assert length(unique(cs)) == 1
    # return cs[1]
end