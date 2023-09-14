export InducedFlag

"""
    InducedFlag{T} <: Flag where {T <: Flag}

Turns a given Flag into its induced equivalent. E.g. `InducedFlag{Graph}(P2)`, where `P2 = Graph(Bool[0 0 1; 0 0 1; 1 1 0])` is the path on three vertices, describes the Flag corresponding to the induced path density. Only makes sense if there is an equivalent to "edges" in the Flag type `T`.
"""
struct InducedFlag{T} <: Flag where {T<:Flag}
    F::T
    InducedFlag{T}(F::T) where {T<:Flag} = new(F)
    InducedFlag{T}(opts...) where {T<:Flag} = new(T(opts...))
    InducedFlag{T}(nothing) where {T<:Flag} = nothing
end

function ==(A::InducedFlag{T}, B::InducedFlag{T}) where {T<:Flag}
    A.F == B.F
end
function hash(A::InducedFlag{T}, h::UInt) where {T<:Flag}
    return hash(A.F, hash(:InducedFlag, h))
end

function Base.one(::Type{InducedFlag{T}})::InducedFlag{T} where {T<:Flag}
    InducedFlag{T}(one(T))
end

function Base.one(F::InducedFlag{T})::InducedFlag{T} where {T<:Flag}
    InducedFlag{T}(one(F.F))
end

Base.size(F::InducedFlag)::Int = size(F.F)

function labelCanonically(F::InducedFlag{T})::InducedFlag{T} where {T<:Flag}
    InducedFlag{T}(label(F.F; removeIsolated=false)[1])
end
function labelCanonically(Fs::Vector{T})::Vector{T} where {T<:InducedFlag}
    labelCanonically.(Fs)
end

function countEdges(F::InducedFlag{T})::Vector{Int} where {T<:Flag}
    return countEdges(F.F)
end

function maxPredicateArguments(::Type{InducedFlag{T}}) where {T<:Flag}
    return maxPredicateArguments(T)
end

function subFlag(F::InducedFlag{T}, vertices::Vector{Int})::InducedFlag{T} where {T<:Flag}
    return InducedFlag{T}(subFlag(F.F, vertices))
end

"""
    glue(F::InducedFlag{T}, G::InducedFlag{T}, p::Vector{Int})

Glues together the two induced Flags `F` and `G`, after applying the permutation `p` to the vertices of `F`. `p` may be a permutation involving more than `size(F)` vertices. Since these Flags describe induced densities, the result is a linear combination of every possible combination of "unknown" edges between the added vertices from eachothers perspectives (or equivalent). If the common part is different, they are orthogonal to each other and thus return an empty Vector.
"""
function glue(F::InducedFlag{T}, G::InducedFlag{T}, p::AbstractVector{Int})::QuantumFlag{InducedFlag{T},Rational{Int}} where {T<:Flag}
    n = size(F)
    m = size(G)

    # Check if the overlap is identical
    commonPartF = [i for (i, c) in enumerate(p[1:n]) if c in 1:m]
    commonPartG = [c for c in p[1:n] if c in 1:m]
    if subFlag(F, commonPartF) != subFlag(G, commonPartG)
        return QuantumFlag{InducedFlag{T},Rational{Int}}()
    end

    # Regular glue 
    FG = glue(F.F, G.F, p)

    if FG === nothing
        return QuantumFlag{InducedFlag{T},Rational{Int}}()
    end

    if U == InducedFlag{T}

        # Determine all ways to combine the leaves
        pred = findUnknownPredicates(FG, [collect(1:m), p[1:n]])

        if length(pred) > 1
            @error "TODO: Multiple predicate types"
        end

        pred = pred[1]

        FGMarked = EdgeMarkedFlag{InducedFlag{T}}(InducedFlag{T}(FG), pred)
        res = sum(c//1*G for (G,c) in zeta(FGMarked).coeff)

        return res
    elseif U == T
        # Convert to non-induced
        predF = [glue(f, FG, p) for f in findUnknownPredicates(F.F, Vector{Int}[])]
        predG = [glue(FG, g, collect(1:size(FG))) for g in findUnknownPredicates(G.F, Vector{Int}[])]
        @views pred = unique(vcat(predF, predG))

        res = QuantumFlag{T,Rational{Int}}(glue(Fs...) => (-1)^length(Fs) for Fs in combinations(pred))
        res.coeff[FG] = 1

        return res
    else
        error("Gluing $(InducedFlag{T}) with target type $U not implemented.")
        return missing
    end
end

function distinguish(F::InducedFlag{T}, v::Int, W::BitVector) where {T<:Flag}
    return distinguish(F.F, v, W)
end

function isolatedVertices(F::InducedFlag{T})::BitVector where {T<:Flag}
    return isolatedVertices(F.F)
end

function addPredicates(F::InducedFlag{T}, p::U, preds::Vararg{U}) where {T<:Flag,U<:Predicate}
    tmp = addPredicates(F.F, p, preds...)
    if tmp === nothing
        return nothing
    end
    InducedFlag{T}(tmp)
end

function permute(F::InducedFlag{T}, p::AbstractVector{Int}) where {T<:Flag}
    InducedFlag{T}(glue(F.F, one(T), p))
end

function findUnknownPredicates(F::InducedFlag{T}, fixed::Vector{U}) where {T<:Flag,U<:AbstractVector{Int}}
    return findUnknownPredicates(F.F, fixed)
end


function isSym(F::InducedFlag, v1::Int, v2::Int)::Bool
    return isSym(F.F, v1, v2)
end

function generateAll(::Type{InducedFlag{F}}, maxVertices::Int, maxPredicates::Vector{Int}) where {F<:Flag}

    tmp = generateAll(F, maxVertices, maxPredicates)
    return [InducedFlag{F}(f) for f in tmp]
end

# Reduction to a basis of induced densities (The quotient of Razborov)
function eliminateIsolated(F::InducedFlag{T}) where {T<:Flag}
    return eliminateIsolated(1*F)
end

function eliminateIsolated(Fs::QuantumFlag{InducedFlag{T},D}) where {T<:Flag, D}
    if length(Fs.coeff) == 0
        return Fs 
    end
    res = QuantumFlag{InducedFlag{T},D}()
    resIsolated = QuantumFlag{InducedFlag{T},D}()
    for (F,c) in Fs.coeff
        v = isolatedVertices(F)
        if !any(v)
            res += D(c) * F
        else
            preds = findUnknownPredicates(F, [(1:size(F))[.!v]])
            markedF = EdgeMarkedFlag{InducedFlag{T}}(F, preds)
            resIsolated += D(c)*(F - zeta(markedF) + labelCanonically(subFlag(F, (1:size(F))[.!v])))
        end
    end
    return res + eliminateIsolated(resIsolated)
end