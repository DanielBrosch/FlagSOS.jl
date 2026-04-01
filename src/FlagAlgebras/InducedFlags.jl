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

function is_up_to_iso(::T) where {T<:Flag}
    return is_up_to_iso(T)
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

function Base.one(
    ::Type{InducedFlag{T,UpToIso}}
)::InducedFlag{T,UpToIso} where {T<:Flag,UpToIso}
    return InducedFlag{T,UpToIso}(one(T))
end

function Base.one(F::InducedFlag{T,UpToIso})::InducedFlag{T,UpToIso} where {T<:Flag,UpToIso}
    return InducedFlag{T,UpToIso}(one(F.F))
end

Base.size(F::InducedFlag)::Int = size(F.F)

function labelCanonically(
    F::InducedFlag{T,UpToIso}
)::InducedFlag{T,UpToIso} where {T<:Flag,UpToIso}
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

function subFlag(
    F::InducedFlag{T,UpToIso}, vertices::AbstractVector{Int}
)::InducedFlag{T,UpToIso} where {T<:Flag,UpToIso}
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
    label=true,
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
        EdgeMarkedFlag{InducedFlag{T,UpToIso},predicateType(InducedFlag{T,UpToIso})},
        Rational{Int},
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
        @assert !label || k == 0
        # @show k
        # @assert Set(commonPartG) == Set(1:k)

        in_fact =
            1 // (
                up_to_iso_fact(PartiallyLabeledFlag(F, k)) *
                up_to_iso_fact(PartiallyLabeledFlag(G, commonPartG))
            )
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

function glueFinite(
    N,
    F::InducedFlag{T,UpToIso},
    G::InducedFlag{T,UpToIso};
    # p::AbstractVector{Int}=vcat(collect((size(G)+1):(size(G)+size(F))), 1:size(G));
    labelFlags=true,
    # isAllowed=(f) -> true,
    base_model=nothing,
    n_outer=size(F) + size(G),
) where {T<:Flag,UpToIso}
    return unlabel(
        glueFinite(
            N,
            PartiallyLabeledFlag(F, 0),
            PartiallyLabeledFlag(G, 0);
            labelFlags=labelFlags,
            base_model=base_model,
            n_outer=n_outer,
        ),
    )
end

function glueFinite(
    N,
    F::PartiallyLabeledFlag{InducedFlag{T,UpToIso}},
    G::PartiallyLabeledFlag{InducedFlag{T,UpToIso}};
    # p::AbstractVector{Int}=vcat(1:(F.n), (size(G)+1):(size(G)+size(F)-F.n));
    labelFlags=true,
    base_model=nothing,
    n_outer=size(F) + size(G) - F.n,
) where {T<:Flag,UpToIso}
    @assert labelFlags

    t = type(F)
    @assert type(G) == t

    lvl = size(F) + size(G) - F.n

    # @show N, F, G, p, T, UpToIso
    # global test = N, F, G, p, T, UpToIso

    @assert base_model !== nothing

    glueDict = if base_model === nothing
        sample_coefficients(
            InducedFlag{T,UpToIso},
            lvl,
            t;
            n_outer=n_outer,
            N=N,
            only_balanced=size(F) == size(G),
            base_model=base_model,
        )[3]
    else
        # @show (InducedFlag{T,UpToIso}, lvl, t, size(F) == size(G))
        get!(base_model.glue_cache, (InducedFlag{T,UpToIso}, lvl, t, size(F) == size(G), n_outer)) do
            sample_coefficients(
                InducedFlag{T,UpToIso},
                lvl,
                t;
                n_outer=n_outer,
                N=N,
                only_balanced=size(F) == size(G),
                base_model=base_model,
            )[3]
        end
    end

    return get(glueDict, (labelCanonically(F), labelCanonically(G)), 0 * F)
end

function glueFinite(
    N,
    F::PartiallyLabeledFlag{PartiallyLabeledFlag{InducedFlag{T,UpToIso}}},
    G::PartiallyLabeledFlag{PartiallyLabeledFlag{InducedFlag{T,UpToIso}}};
    # p::AbstractVector{Int}=vcat(1:(F.n), (size(G)+1):(size(G)+size(F)-F.n));
    labelFlags=true,
    base_model=nothing,
    n_outer=size(F) + size(G) - F.n
) where {T<:Flag,UpToIso}
    @assert labelFlags

    inner_n = F.F.n
    @assert inner_n == G.F.n

    F_no_inner_label = PartiallyLabeledFlag{InducedFlag{T,UpToIso}}(F.F.F, F.n)
    G_no_inner_label = PartiallyLabeledFlag{InducedFlag{T,UpToIso}}(G.F.F, G.n)

    FG = glueFinite(
        N, F_no_inner_label, G_no_inner_label; labelFlags=labelFlags, base_model=base_model, n_outer=n_outer
    )

    return sum(
        c * PartiallyLabeledFlag{PartiallyLabeledFlag{InducedFlag{T,UpToIso}}}(
            PartiallyLabeledFlag{InducedFlag{T,UpToIso}}(f.F, inner_n), f.n
        ) for (f, c) in FG.coeff
    )
end

# function glueFinite(
#     N,
#     F::PartiallyLabeledFlag{InducedFlag{T,UpToIso}},
#     G::PartiallyLabeledFlag{InducedFlag{T,UpToIso}},
#     p::AbstractVector{Int}=vcat(1:(F.n), (size(G)+1):(size(G)+size(F)-F.n));
#     labelFlags=true,
#     isAllowed=(f) -> true,
# ) where {T<:Flag,UpToIso}
#     # @show N, F, G, p
#     # @show glueFinite_internal(N, PartiallyLabeledFlag(F.F.F, F.n), PartiallyLabeledFlag(G.F.F, G.n), p; labelFlags=false, isAllowed=isAllowed)
#     # @show tmp = glueFinite_internal(
#     #         N, toNonInduced(F), toNonInduced(G), p; labelFlags=false, isAllowed=isAllowed
#     #     )
#     # @show tmp = toInduced(tmp)
#     # @show typeof(tmp)
#     # @show labelCanonically(tmp)

#     res = toInduced(
#         glueFinite(
#             N, toNonInduced(F), toNonInduced(G), p; labelFlags=false, isAllowed=isAllowed
#         ),
#         UpToIso,
#     )
#     if labelFlags
#         return labelCanonically(res)
#     end
#     return res
# end

function distinguish(
    F::InducedFlag{T,UpToIso}, v::Int, W::BitVector
)::UInt where {T<:Flag,UpToIso}
    return distinguish(F.F, v, W)
end

function isolatedVertices(F::InducedFlag{T,UpToIso})::BitVector where {T<:Flag,UpToIso}
    return isolatedVertices(F.F)
end

function isAllowed(F::InducedFlag{T,UpToIso}, e) where {T<:Flag,UpToIso}
    return isAllowed(F.F, e)
end

function addPredicates(
    F::InducedFlag{T,UpToIso}, preds::Vector{U}
) where {T<:Flag,U<:Predicate,UpToIso}
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

function eliminateIsolated(
    Fs::QuantumFlag{InducedFlag{T,UpToIso},D}
) where {T<:Flag,D,UpToIso}
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
function toInduced(F::Union{T,QuantumFlag{T}}, UpToIso=true) where {T<:Flag}
    tmp = zeta(F)
    res = QuantumFlag{InducedFlag{T,UpToIso},Int}()
    for (G, c) in tmp.coeff
        fact = UpToIso ? up_to_iso_fact(G) : 1
        res += c * fact * InducedFlag{T,UpToIso}(G)
    end
    return res
end

function toNonInduced(
    F::QuantumFlag{InducedFlag{T,UpToIso}}
) where {T<:Flag,UpToIso}
    return sum(c * toNonInduced(f) for (f, c) in F.coeff)
end

function toNonInduced(
    F::InducedFlag{T,UpToIso}
) where {T<:Flag,UpToIso}
    tmp = moebius(F)
    res = QuantumFlag{T,Int}()
    fact = UpToIso ? 1 // up_to_iso_fact(F) : 1
    for (G, c) in tmp.coeff
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

function toInduced(
    F::Union{PartiallyLabeledFlag{T},QuantumFlag{PartiallyLabeledFlag{T}}}, UpToIso=true
) where {T<:Flag}
    tmp = zeta(F)
    res = QuantumFlag{PartiallyLabeledFlag{InducedFlag{T,UpToIso}},Int}()
    for (G, c) in tmp.coeff
        GL = PartiallyLabeledFlag{InducedFlag{T,UpToIso}}(InducedFlag{T,UpToIso}(G.F), G.n)
        fact = UpToIso ? up_to_iso_fact(GL) : 1
        res += c * fact * GL
    end
    return res
end

function toNonInduced(
    F::QuantumFlag{PartiallyLabeledFlag{InducedFlag{T,UpToIso}}}
) where {T<:Flag,UpToIso}
    return sum(c*toNonInduced(f) for (f,c) in F.coeff)
end

function toNonInduced(
    F::PartiallyLabeledFlag{InducedFlag{T,UpToIso}}
) where {T<:Flag,UpToIso}
    tmp = moebius(F)
    res = QuantumFlag{PartiallyLabeledFlag{T},Int}()
    fact = UpToIso ? 1 // up_to_iso_fact(F) : 1
    for (G, c) in tmp.coeff
        res += fact * c * PartiallyLabeledFlag(G.F.F, G.n)
    end
    return res
end

function labelCanonically(
    F::PartiallyLabeledFlag{InducedFlag{T,UpToIso}}
)::PartiallyLabeledFlag{InducedFlag{T,UpToIso}} where {T<:Flag,UpToIso}
    return label(F; removeIsolated=false)[1]
end

function sample_coefficients_old(
    ::Type{InducedFlag{T,UpToIso}},
    n::Int,
    type::InducedFlag{T,UpToIso};
    n_outer::Int=n,
    base_model=nothing,
    all_flags::Vector{PartiallyLabeledFlag{InducedFlag{T,UpToIso}}}=generateAll(
        PartiallyLabeledFlag{InducedFlag{T,UpToIso}},
        n,
        [size(type), 10000];
        initial_flag=PartiallyLabeledFlag{InducedFlag{T,UpToIso}}(type, size(type)),
        withProperty=x -> isAllowed(base_model, x),
        withPropertyMarked=x -> isAllowed(base_model, x),
    ),
    N=:limit,
    only_balanced=true,
) where {T<:Flag,UpToIso}
    @info "Sampling $T for n=$n of type $type"
    @assert UpToIso
    k = size(type)

    only_balanced && @assert iseven(n - k)
    t = only_balanced ? Int((n - k) / 2) : n

    idx_flags = only_balanced ? filter(x -> size(x) == t + k, all_flags) : all_flags
    glue_flags = N == :limit ? filter(x -> size(x) == n, all_flags) : all_flags

    res = Dict()

    for t1 in 0:(n-k)
        only_balanced && t1 != t && continue
        t2 = n - k - t1

        for G in glue_flags
            nG = size(G)
            n_free = nG - k

            ov = t1 + t2 - n_free

            @assert n_free == t1 + t2 - ov

            # Number of ways to place the two sets of free verts
            fact = if N == :limit
                1 // (binomial(n_free, t1))
            else
                1 // (
                    binomial(n_free, ov) *
                    binomial(n_free - ov, t1 - ov) *
                    binomial(n_free - t1, t2 - ov)
                )
            end

            # Probability to hit n_free many vertices
            fact2 = if N == :limit
                1 // 1
            else
                (
                    binomial(N - k, ov) *
                    binomial(N - k - ov, t1 - ov) *
                    binomial(N - k - t1, t2 - ov)
                ) // (binomial(N - k, t1) * binomial(N - k, t2))
            end
            # if ov > 0 
            #     fact2 *= 2
            # end
            for c in combinations((k+1):nG, t1)
                # @show n, t, c, vcat(1:k, c), G
                F1 = labelCanonically(subFlag(G, vcat(1:k, c)))

                # zero, unless finite FA
                other_inds = setdiff((k+1):nG, c)

                for d in combinations(c, ov)
                    # @show n, nG, t, ov, c, d, other_inds, fact2
                    F2 = labelCanonically(subFlag(G, sort!(vcat(1:k, d, other_inds))))
                    # @show F1
                    # @show F2
                    @assert size(F1) == t1 + k
                    @assert size(F2) == t2 + k
                    res[(F1, F2)] =
                        get(
                            res,
                            (F1, F2),
                            QuantumFlag{
                                PartiallyLabeledFlag{InducedFlag{T,UpToIso}},Rational{Int}
                            }(),# - glueFinite(N, F1, F2),
                        ) + fact * fact2 * G
                end
            end
        end
    end

    return idx_flags, glue_flags, res
end

function sample_coefficients(
    ::Type{InducedFlag{T,UpToIso}},
    n::Int,
    type::InducedFlag{T,UpToIso};
    n_outer::Int=n,
    base_model=nothing,
    all_flags::Vector{PartiallyLabeledFlag{InducedFlag{T,UpToIso}}}=generateAll(
        PartiallyLabeledFlag{InducedFlag{T,UpToIso}},
        n_outer,
        [size(type), 10000];
        initial_flag=PartiallyLabeledFlag{InducedFlag{T,UpToIso}}(type, size(type)),
        withProperty=x -> isAllowed(base_model, x),
        withPropertyMarked=x -> isAllowed(base_model, x),
    ),
    N=:limit,
    only_balanced=true,
) where {T<:Flag,UpToIso}
    @info "Sampling $T for n=$n@$n_outer of type $type"
    @assert UpToIso
    k = size(type)

    only_balanced && @assert iseven(n - k)
    t = only_balanced ? Int((n - k) / 2) : n

    idx_flags = only_balanced ? filter(x -> size(x) == t + k, all_flags) : all_flags
    # glue_flags = N == :limit ? filter(x -> size(x) == n_outer, all_flags) : all_flags
    glue_flags = filter(x -> size(x) == n_outer, all_flags)

    res = ThreadSafeDict()

    @show length(glue_flags)

    n_additional = n_outer - n
    @assert n_additional >= 0

    for t1 in 0:(n-k)
        only_balanced && t1 != t && continue

        for G in glue_flags
            nG = size(G)
            n_free = nG - k

            Threads.@threads for c in collect(combinations((k+1):nG, t1))
                F1 = labelCanonically(subFlag(G, vcat(1:k, c)))

                other = N == :limit ? setdiff((k+1):nG, c) : ((k+1):nG)

                # k + t1 + t2 <= n
                # t2 <= n - k - t1
                for t2 in 0:(n-k-t1)
                # for t2 in 0:(n-k)

                    only_balanced && t2 != t && continue

                    for d in combinations(other, t2)
                        F2 = labelCanonically(subFlag(G, sort!(vcat(1:k, d))))

                        ov = N == :limit ? 0 : length(intersect(c, d))

                        # Number of ways to place the two sets of free verts
                        # fact = if N == :limit
                        #     1 // (binomial(n_free, t1))
                        # else
                        # end
                        fact =
                            1 // (
                                binomial(n_free, ov) *
                                binomial(n_free - ov, t1 - ov) *
                                binomial(n_free - t1, t2 - ov)
                                # binomial(n_free+n_additional, n_free)
                            )

                        # Probability to hit n_free many vertices
                        fact2 = if N == :limit
                            1 // 1
                        else
                            (
                                binomial(N - k, ov) *
                                binomial(N - k - ov, t1 - ov) *
                                binomial(N - k - t1, t2 - ov)
                            ) // (binomial(N - k, t1) * binomial(N - k, t2))
                        end

                        res[(F1, F2)] =
                            get(
                                res,
                                (F1, F2),
                                QuantumFlag{
                                    PartiallyLabeledFlag{InducedFlag{T,UpToIso}},
                                    Rational{Int},
                                }(),# - glueFinite(N, F1, F2),
                            ) + fact * fact2 * G

                    end

                end
            end

            # for ov in 0:(N == :limit ? 0 : t1)
            #     t2 = n - k - t1 + ov

            #     # ov = t1 + t2 - n_free + n_additional
            #     @assert ov >= 0

            #     @show n_free, t1, t2, ov, n_additional
            #     @assert n_free == t1 + t2 - ov + n_additional

            #     # if ov > 0 
            #     #     fact2 *= 2
            #     # end
            #     # @show n, t, c, vcat(1:k, c), G
            #     F1 = labelCanonically(subFlag(G, vcat(1:k, c)))

            #     # zero, unless finite FA
            #     remaining_inds = setdiff((k+1):nG, c)

            #     for other_inds in combinations(remaining_inds, t2 - ov)
            #         for d in combinations(c, ov)
            #             # @show n, nG, t, ov, c, d, other_inds, fact2
            #             F2 = labelCanonically(subFlag(G, sort!(vcat(1:k, d, other_inds))))
            #             # @show F1
            #             # @show F2
            #             @assert size(F1) == t1 + k
            #             @assert size(F2) == t2 + k
            #             res[(F1, F2)] =
            #                 get(
            #                     res,
            #                     (F1, F2),
            #                     QuantumFlag{
            #                         PartiallyLabeledFlag{InducedFlag{T,UpToIso}},
            #                         Rational{Int},
            #                     }(),# - glueFinite(N, F1, F2),
            #                 ) + fact * fact2 * G
            #         end

            #     end
            # end
        end
    end

    return idx_flags, glue_flags, res
end