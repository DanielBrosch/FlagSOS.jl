export InducedFlag, toInduced, toNonInduced

"""
    InducedFlag{T, UpToIso} <: Flag where {T <: Flag}

Turns a given Flag into its induced equivalent. E.g. `InducedFlag{Graph}(P2)`, where `P2 = Graph(Bool[0 0 1; 0 0 1; 1 1 0])` is the path on three vertices, describes the Flag corresponding to the induced path density. Only makes sense if there is an equivalent to "edges" in the Flag type `T`.
"""
struct InducedFlag{T,UpToIso} <: Flag where {T<:Flag,UpToIso}
    F::T
    InducedFlag(F::T) where {T<:Flag} = InducedFlag{T,true}(F)
    InducedFlag{T}(F::T) where {T<:Flag} = InducedFlag{T,true}(F)
    InducedFlag{T,UpToIso}(F::T) where {T<:Flag,UpToIso} = new(F)
    InducedFlag{T}(opts...) where {T<:Flag} = InducedFlag{T,true}(opts...)
    InducedFlag{T,UpToIso}(opts...) where {T<:Flag,UpToIso} = new(T(opts...))
    InducedFlag{T}(::Nothing) where {T<:Flag} = nothing
    InducedFlag{T,UpToIso}(::Nothing) where {T<:Flag,UpToIso} = nothing
end

# const InducedFlag{T} = InducedFlag{T,true}

function Base.show(io::IO, F::InducedFlag{T,UpToIso}) where {T<:Flag,UpToIso}
    return print(io, "I$(F.F)")
end

function is_up_to_iso(::Type{T}) where {T<:Flag}
    return false
end


function is_up_to_iso(::Type{InducedFlag{T,true}}) where {T<:Flag}
    return true
end



function ==(A::InducedFlag{T,UpToIso}, B::InducedFlag{T,UpToIso}) where {T<:Flag,UpToIso}
    return A.F == B.F
end
function hash(A::InducedFlag{T,UpToIso}, h::UInt) where {T<:Flag,UpToIso}
    return hash(A.F, hash(:InducedFlag, h))
end

function Base.one(::Type{InducedFlag{T,UpToIso}})::InducedFlag{T,UpToIso} where {T<:Flag,UpToIso}
    return InducedFlag{T,UpToIso}(one(T))
end

function Base.one(F::InducedFlag{T,UpToIso})::InducedFlag{T,UpToIso} where {T<:Flag,UpToIso}
    return InducedFlag{T,UpToIso}(one(F.F))
end

Base.size(F::InducedFlag)::Int = size(F.F)

function labelCanonically(F::InducedFlag{T,UpToIso})::InducedFlag{T,UpToIso} where {T<:Flag,UpToIso}
    return InducedFlag{T,UpToIso}(label(F.F; removeIsolated=false)[1])
end

function countEdges(F::InducedFlag{T,UpToIso})::Vector{Int} where {T<:Flag,UpToIso}
    return countEdges(F.F)
end

function maxPredicateArguments(::Type{InducedFlag{T,UpToIso}}) where {T<:Flag,UpToIso}
    return maxPredicateArguments(T)
end

function predicateType(::Type{InducedFlag{T,UpToIso}}) where {T<:Flag,UpToIso}
    return predicateType(T)
end

function subFlag(F::InducedFlag{T,UpToIso}, vertices::AbstractVector{Int})::InducedFlag{T,UpToIso} where {T<:Flag,UpToIso}
    return InducedFlag{T,UpToIso}(subFlag(F.F, vertices))
end

function up_to_iso_fact(F::T) where {T<:Flag}
    return aut(F).size // factorial(size(F))
end



"""
    glue(F::InducedFlag{T, UpToIso}, G::InducedFlag{T, UpToIso}, p::Vector{Int})

Glues together the two induced Flags `F` and `G`, after applying the permutation `p` to the vertices of `F`. `p` may be a permutation involving more than `size(F)` vertices. Since these Flags describe induced densities, the result is a linear combination of every possible combination of "unknown" edges between the added vertices from eachothers perspectives (or equivalent). If the common part is different, they are orthogonal to each other and thus return an empty Vector.
"""
function glue(
    F::InducedFlag{T,UpToIso},
    G::InducedFlag{T,UpToIso},
    p::AbstractVector{Int};
    isAllowed=(f) -> true,
    label=true
)::QuantumFlag{InducedFlag{T,UpToIso},Rational{Int}} where {T<:Flag,UpToIso}
    n = size(F)
    m = size(G)

    # Check if the overlap is identical
    commonPartF = [i for (i, c) in enumerate(p[1:n]) if c in 1:m]
    commonPartG = [c for c in p[1:n] if c in 1:m]
    if subFlag(F, commonPartF) != subFlag(G, commonPartG)
        return QuantumFlag{InducedFlag{T,UpToIso},Rational{Int}}()
    end

    # Regular glue 
    fg = glue(F.F, G.F, p)#; isAllowed = isAllowed)

    if fg === nothing
        return QuantumFlag{InducedFlag{T,UpToIso},Rational{Int}}()
    end

    # if U == InducedFlag{T, UpToIso}

    if !(fg isa QuantumFlag)
        fg = 1 // 1 * fg
    end

    res = QuantumFlag{InducedFlag{T,UpToIso},Rational{Int}}()

    tmp = QuantumFlag{
        EdgeMarkedFlag{InducedFlag{T,UpToIso},predicateType(InducedFlag{T,UpToIso})},Rational{Int}
    }()

    for (FG, c) in fg.coeff

        # Determine all ways to combine the leaves of the sunflower
        pred = findUnknownPredicates(FG, [collect(1:m), p[1:n]])

        if length(pred) > 1
            @error "TODO: Multiple predicate types"
        end

        pred = pred[1]

        FGMarked = EdgeMarkedFlag{InducedFlag{T,UpToIso}}(InducedFlag{T,UpToIso}(FG), pred)
        tmp += (c // 1) * FGMarked
        # res += sum(c//1 * G for (G, c) in zeta(FGMarked; label=true, isAllowed=isAllowed).coeff)
    end

    if label
        tmp = labelCanonically(tmp)
    end
    res = zeta(tmp; label=label, isAllowed=isAllowed)
    if UpToIso

        # @show F, G, p
        k = length(commonPartF)
        # @show k
        # @assert Set(commonPartG) == Set(1:k)

        in_fact = 1 // (up_to_iso_fact(PartiallyLabeledFlag(F, k)) * up_to_iso_fact(PartiallyLabeledFlag(G, commonPartG)))
        # in_fact = 1 // (up_to_iso_fact(PartiallyLabeledFlag(F, k)) * up_to_iso_fact(PartiallyLabeledFlag(G, k)))

        for f in keys(res.coeff)
            # @show f, in_fact, up_to_iso_fact(PartiallyLabeledFlag(f, k))
            res.coeff[f] *= in_fact * up_to_iso_fact(PartiallyLabeledFlag(f, k))
        end
    end

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
    #     error("Gluing $(InducedFlag{T, UpToIso}) with target type $U not implemented.")
    #     return missing
    # end
end

function distinguish(F::InducedFlag{T,UpToIso}, v::Int, W::BitVector)::UInt where {T<:Flag,UpToIso}
    return distinguish(F.F, v, W)
end

function isolatedVertices(F::InducedFlag{T,UpToIso})::BitVector where {T<:Flag,UpToIso}
    return isolatedVertices(F.F)
end

function isAllowed(F::InducedFlag{T,UpToIso}, e) where {T<:Flag,UpToIso}
    return isAllowed(F.F, e)
end

function addPredicates(F::InducedFlag{T,UpToIso}, preds::Vector{U}) where {T<:Flag,U<:Predicate,UpToIso}
    tmp = addPredicates(F.F, preds)
    if tmp === nothing
        return nothing
    end
    if tmp isa Vector
        return [InducedFlag{T,UpToIso}(f) for f in tmp]
    end
    return InducedFlag{T,UpToIso}(tmp)
end

function permute(F::InducedFlag{T,UpToIso}, p::AbstractVector{Int}) where {T<:Flag,UpToIso}
    # return InducedFlag{T, UpToIso}(glue(F.F, one(T), p))
    return InducedFlag{T,UpToIso}(permute(F.F, p))
end

function findUnknownPredicates(
    F::InducedFlag{T,UpToIso}, fixed::Vector{U}, predLimits::Vector
) where {T<:Flag,U<:AbstractVector{Int},UpToIso}
    return findUnknownPredicates(F.F, fixed, predLimits)
end

function isSym(F::InducedFlag, v1::Int, v2::Int)::Bool
    return isSym(F.F, v1, v2)
end

# function generateAll(
#     ::Type{InducedFlag{F}}, maxVertices::Int, maxPredicates::Vector{Int}
# ) where {F<:Flag}
#     tmp = generateAll(F, maxVertices, maxPredicates)
#     return [InducedFlag{F}(f) for f in tmp]
# end

# Reduction to a basis of induced densities (The quotient of Razborov)
function eliminateIsolated(F::InducedFlag{T,UpToIso}) where {T<:Flag,UpToIso}
    return eliminateIsolated(1 * F)
end

function eliminateIsolated(Fs::QuantumFlag{InducedFlag{T,UpToIso},D}) where {T<:Flag,D,UpToIso}
    if length(Fs.coeff) == 0
        return Fs
    end
    res = QuantumFlag{InducedFlag{T,UpToIso},D}()
    resIsolated = QuantumFlag{InducedFlag{T,UpToIso},D}()
    for (F, c) in Fs.coeff
        v = isolatedVertices(F)
        if !any(v)
            res += D(c) * F
        else
            preds = findUnknownPredicates(F, [(1:size(F))[.!v]])
            markedF = EdgeMarkedFlag{InducedFlag{T,UpToIso}}(F, preds)
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
function toInduced(F::Union{T,QuantumFlag{T}}, UpToIso = true) where {T<:Flag}
    tmp = zeta(F)
    res = QuantumFlag{InducedFlag{T,UpToIso},Int}()
    for (G, c) in tmp.coeff
        fact = UpToIso ? up_to_iso_fact(G) : 1
        res += c * fact * InducedFlag{T,UpToIso}(G)
    end
    return res
end

function toNonInduced(F::Union{InducedFlag{T,UpToIso},QuantumFlag{InducedFlag{T,UpToIso}}}) where {T<:Flag,UpToIso}
    tmp = moebius(F)
    res = QuantumFlag{T,Int}()
    for (G, c) in tmp.coeff
        fact = UpToIso ? 1//up_to_iso_fact(G) : 1
        res += fact * c * G.F
    end
    return res
end

function isInducedFlag(T)
    return T <: InducedFlag
end

# For quotienting out linear dependencies
# E.g. adding isolated vertices results in a quantum flag equivalent to the original flag
function quotient(Fs::Vector{T}, isAllowed=(f) -> true) where {T<:Flag,UpToIso}
    oneVert = permute(T(), [1])
    # @show oneVert

    # @show Fs

    n = maximum(size.(Fs); init=1)

    res = QuantumFlag{T,Rational{Int}}[]
    # res = Dict()
    ek = 1 * T()
    for newVerts in 1:n
        ek = ek * oneVert
        @error "Better to do vertex by vertex, filter by allowed every time"
        for f in Fs
            size(f) + newVerts > n && continue
            tmp = labelCanonically(ek * f - 1 // 1 * f)
            # size(f) == n && continue
            # if newVerts == 1
            #     tmp = labelCanonically(oneVert * f - 1//1 * f)
            # else
            #     tmp = labelCanonically(oneVert * (oneVert * f) - 1//1 * f)
            # end
            # @show tmp
            # if any(tmp.coeff) do (G, _)
            #     isAllowed(G) && !in(G, Fs)
            # end
            #     @info "Missing some flags to eliminate product of $f"
            #     continue
            # end
            # res[f] = tmp
            filter!(x -> isAllowed(x.first), tmp.coeff)
            # @show length(res) + 1
            # @show f
            # @show oneVert * f
            if !iszero(tmp)
                push!(res, labelCanonically(tmp))
            end
            break
        end
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


function unlabel(F::PartiallyLabeledFlag{InducedFlag{T,true}}) where {T<:Flag}
    return (factorial(size(F) - F.n) // factorial(size(F))) * (aut(F.F).size // aut(F).size) * F.F
end


function labelCanonically(
    F::PartiallyLabeledFlag{InducedFlag{T,UpToIso}}
)::PartiallyLabeledFlag{InducedFlag{T,UpToIso}} where {T<:Flag,UpToIso}
    return label(F; removeIsolated=false)[1]
end

function sample_coefficients(::Type{InducedFlag{T}}, n::Int, type::T; all_flags::Vector{PartiallyLabeledFlag{T}}=generateAll(PartiallyLabeledFlag{T}, n, [size(type), 10000]; initial_flag=PartiallyLabeledFlag{T}(type, size(type)))) where {T<:Flag}
    return all_flags
end