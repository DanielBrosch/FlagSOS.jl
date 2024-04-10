export InducedFlag, toInduced, toNonInduced

"""
    InducedFlag{T} <: Flag where {T <: Flag}

Turns a given Flag into its induced equivalent. E.g. `InducedFlag{Graph}(P2)`, where `P2 = Graph(Bool[0 0 1; 0 0 1; 1 1 0])` is the path on three vertices, describes the Flag corresponding to the induced path density. Only makes sense if there is an equivalent to "edges" in the Flag type `T`.
"""
struct InducedFlag{T} <: Flag where {T<:Flag}
    F::T
    InducedFlag{T}(F::T) where {T<:Flag} = new(F)
    InducedFlag{T}(opts...) where {T<:Flag} = new(T(opts...))
    InducedFlag{T}(::Nothing) where {T<:Flag} = nothing
end

function ==(A::InducedFlag{T}, B::InducedFlag{T}) where {T<:Flag}
    return A.F == B.F
end
function hash(A::InducedFlag{T}, h::UInt) where {T<:Flag}
    return hash(A.F, hash(:InducedFlag, h))
end

function Base.one(::Type{InducedFlag{T}})::InducedFlag{T} where {T<:Flag}
    return InducedFlag{T}(one(T))
end

function Base.one(F::InducedFlag{T})::InducedFlag{T} where {T<:Flag}
    return InducedFlag{T}(one(F.F))
end

Base.size(F::InducedFlag)::Int = size(F.F)

function labelCanonically(F::InducedFlag{T})::InducedFlag{T} where {T<:Flag}
    return InducedFlag{T}(label(F.F; removeIsolated=false)[1])
end

function countEdges(F::InducedFlag{T})::Vector{Int} where {T<:Flag}
    return countEdges(F.F)
end

function maxPredicateArguments(::Type{InducedFlag{T}}) where {T<:Flag}
    return maxPredicateArguments(T)
end

function predicateType(::Type{InducedFlag{T}}) where {T<:Flag}
    return predicateType(T)
end

function subFlag(F::InducedFlag{T}, vertices::Vector{Int})::InducedFlag{T} where {T<:Flag}
    return InducedFlag{T}(subFlag(F.F, vertices))
end

"""
    glue(F::InducedFlag{T}, G::InducedFlag{T}, p::Vector{Int})

Glues together the two induced Flags `F` and `G`, after applying the permutation `p` to the vertices of `F`. `p` may be a permutation involving more than `size(F)` vertices. Since these Flags describe induced densities, the result is a linear combination of every possible combination of "unknown" edges between the added vertices from eachothers perspectives (or equivalent). If the common part is different, they are orthogonal to each other and thus return an empty Vector.
"""
function glue(
    F::InducedFlag{T}, G::InducedFlag{T}, p::AbstractVector{Int}
)::QuantumFlag{InducedFlag{T},Rational{Int}} where {T<:Flag}
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

    # if U == InducedFlag{T}

    # Determine all ways to combine the leaves
    pred = findUnknownPredicates(FG, [collect(1:m), p[1:n]])

    if length(pred) > 1
        @error "TODO: Multiple predicate types"
    end

    pred = pred[1]

    FGMarked = EdgeMarkedFlag{InducedFlag{T}}(InducedFlag{T}(FG), pred)
    res = sum(c//1 * G for (G, c) in zeta(FGMarked; label=true).coeff)

    return res
    # elseif U == T
    #     # Convert to non-induced
    #     predF = [glue(f, FG, p) for f in findUnknownPredicates(F.F, Vector{Int}[])]
    #     predG = [
    #         glue(FG, g, collect(1:size(FG))) for
    #         g in findUnknownPredicates(G.F, Vector{Int}[])
    #     ]
    #     @views pred = unique(vcat(predF, predG))

    #     res = QuantumFlag{T,Rational{Int}}(
    #         glue(Fs...) => (-1)^length(Fs) for Fs in combinations(pred)
    #     )
    #     res.coeff[FG] = 1

    #     return res
    # else
    #     error("Gluing $(InducedFlag{T}) with target type $U not implemented.")
    #     return missing
    # end
end

function distinguish(F::InducedFlag{T}, v::Int, W::BitVector)::UInt where {T<:Flag}
    return distinguish(F.F, v, W)
end

function isolatedVertices(F::InducedFlag{T})::BitVector where {T<:Flag}
    return isolatedVertices(F.F)
end

function addPredicates(F::InducedFlag{T}, preds::Vector{U}) where {T<:Flag,U<:Predicate}
    tmp = addPredicates(F.F, preds)
    if tmp === nothing
        return nothing
    end
    return InducedFlag{T}(tmp)
end

function permute(F::InducedFlag{T}, p::AbstractVector{Int}) where {T<:Flag}
    return InducedFlag{T}(glue(F.F, one(T), p))
end

function findUnknownPredicates(
    F::InducedFlag{T}, fixed::Vector{U}, predLimits::Vector
) where {T<:Flag,U<:AbstractVector{Int}}
    return findUnknownPredicates(F.F, fixed, predLimits)
end

function isSym(F::InducedFlag, v1::Int, v2::Int)::Bool
    return isSym(F.F, v1, v2)
end

function generateAll(
    ::Type{InducedFlag{F}}, maxVertices::Int, maxPredicates::Vector{Int}
) where {F<:Flag}
    tmp = generateAll(F, maxVertices, maxPredicates)
    return [InducedFlag{F}(f) for f in tmp]
end

# Reduction to a basis of induced densities (The quotient of Razborov)
function eliminateIsolated(F::InducedFlag{T}) where {T<:Flag}
    return eliminateIsolated(1 * F)
end

function eliminateIsolated(Fs::QuantumFlag{InducedFlag{T},D}) where {T<:Flag,D}
    if length(Fs.coeff) == 0
        return Fs
    end
    res = QuantumFlag{InducedFlag{T},D}()
    resIsolated = QuantumFlag{InducedFlag{T},D}()
    for (F, c) in Fs.coeff
        v = isolatedVertices(F)
        if !any(v)
            res += D(c) * F
        else
            preds = findUnknownPredicates(F, [(1:size(F))[.!v]])
            markedF = EdgeMarkedFlag{InducedFlag{T}}(F, preds)
            resIsolated +=
                D(c) * (
                    F - zeta(markedF; label=true) +
                    labelCanonically(subFlag(F, (1:size(F))[.!v]))
                )
        end
    end
    return res + eliminateIsolated(resIsolated)
end

# Switching between induced and non-induced
function toInduced(F::Union{T,QuantumFlag{T}}) where {T<:Flag}
    tmp = zeta(F)
    res = QuantumFlag{InducedFlag{T},Int}()
    for (G, c) in tmp.coeff
        res += c * InducedFlag{T}(G)
    end
    return res
end

function toNonInduced(F::Union{InducedFlag{T},QuantumFlag{InducedFlag{T}}}) where {T<:Flag}
    tmp = moebius(F)
    res = QuantumFlag{T,Int}()
    for (G, c) in tmp.coeff
        res += c * G.F
    end
    return res
end

function isInducedFlag(T)
    return T <: InducedFlag
end

# For quotienting out linear dependencies
# E.g. adding isolated vertices results in a quantum flag equivalent to the original flag
function quotient(Fs::Vector{T}, isAllowed=(f) -> true) where {T<:Flag}
    oneVert = permute(T(), [1])
    @show oneVert

    @show Fs

    n = maximum(size.(Fs); init = 1)

    res = QuantumFlag{T, Rational{Int}}[]
    # res = Dict()
    for f in Fs
        size(f) == n && continue
        tmp = oneVert * f
        if any(tmp.coeff) do (G, _)
            isAllowed(G) && !in(G, Fs)
        end
            @info "Missing some flags to eliminate product of $f"
            continue
        end
        # res[f] = tmp
        @show length(res) + 1
        @show f 
        @show oneVert * f
        push!(res, tmp - 1//1 * f)
    end
    return res
    # n = length(Fs)
    # m = length(res)
    # A = zeros(Rational{Int}, m,n)
    # display(res)
    # for (f, g) in res 
    #     i = findfirst(x->x==f, Fs)
    #     A[i, findfirst(x->x==f, Fs)] = 1
    #     @show f
    #     @show g.coeff
    #     for (h, c) in g.coeff
    #         A[i, findfirst(x->x==h, Fs)] = -c 
    #     end
    # end
    # display(A)

    # for i = m:-1:1
    #     j = findlast(x->!iszero(x), A[i, :])
    #     A[i, :] .//= A[i, j]
    #     @show (i,j)
    #     for k = m:-1:1
    #         k == i && continue
    #         A[k, :] -= A[k, j] * A[i, :]
    #     end
    # end
    # A
end
