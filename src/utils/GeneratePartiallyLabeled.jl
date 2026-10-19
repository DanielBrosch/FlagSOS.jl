# These types have unrestricted vertex permutations and add predicates only
# involving the new vertex. Other flag algebras keep the incremental generator.
_unlabeled_generation_supported(::Type) = false
_unlabeled_generation_supported(::Type{Graph}) = true
_unlabeled_generation_supported(::Type{ConstantWeightCode{W,D}}) where {W,D} = W > 0
function _unlabeled_generation_supported(::Type{InducedFlag{T,U}}) where {T,U}
    return _unlabeled_generation_supported(T)
end

function _can_generate_unlabeled(
    ::Type{PartiallyLabeledFlag{T}}, initial_flag::PartiallyLabeledFlag{T}, maxPredicates
) where {T}
    return _unlabeled_generation_supported(T) && length(maxPredicates) == 2 &&
           maxPredicates[1] isa Int && maxPredicates[2] isa Int &&
           hasAtMostEdges(initial_flag, maxPredicates)
end

# Unlike arbitrary callbacks, these model restrictions are invariant under
# forgetting labels. Store a snapshot of the forbidden set, not the mutable
# model: equal restrictions can share cached generations, and adding a forbidden
# flag must not reuse a result generated under the old restrictions.
struct _GenerationForbidden{T<:InducedFlag}
    flags::Set{T}
end

Base.:(==)(a::_GenerationForbidden, b::_GenerationForbidden) = a.flags == b.flags
Base.isequal(a::_GenerationForbidden, b::_GenerationForbidden) = isequal(a.flags, b.flags)
Base.hash(p::_GenerationForbidden, h::UInt) = hash(p.flags, hash(:_GenerationForbidden, h))

_generation_forbidden_match(forbidden, F) = isSubFlag(forbidden, F)

function _generation_forbidden_match(
    forbidden::T, F::Union{T,EdgeMarkedFlag{T},EdgeMarkedFlag{PartiallyLabeledFlag{T}}},
) where {T<:InducedFlag{Graph}}
    m = size(forbidden)
    m > size(F) && return false
    A = forbidden.F.A
    edge = m > 1 && A[1, 2]
    # Cliques and independent sets need no isomorphism test. These dominate
    # Ramsey models, where canonicalizing every candidate subset is expensive.
    for v in 1:m
        A[v, v] && return isSubFlag(forbidden, F)
        for u in 1:(v - 1)
            A[u, v] == edge || return isSubFlag(forbidden, F)
        end
    end
    raw = F isa EdgeMarkedFlag ? F.F : F
    raw = raw isa PartiallyLabeledFlag ? raw.F : raw
    B = raw.F.A
    for vertices in combinations(1:size(F), m)
        # In an induced flag, a missing edge is final only when it is no longer
        # marked. Pruning an unfinished independent set would lose extensions.
        F isa EdgeMarkedFlag && !finalized_subgraph(F, vertices) && continue
        matches = true
        for (i, v) in enumerate(vertices)
            if B[v, v]
                matches = false
                break
            end
            for j in 1:(i - 1)
                if B[vertices[j], v] != edge
                    matches = false
                    break
                end
            end
            matches || break
        end
        matches && return true
    end
    return false
end

function (p::_GenerationForbidden{T})(F::T) where {T}
    return isAllowed(F) && !any(forbidden -> _generation_forbidden_match(forbidden, F), p.flags)
end

function (p::_GenerationForbidden{T})(
    F::Union{EdgeMarkedFlag{T},EdgeMarkedFlag{PartiallyLabeledFlag{T}}},
) where {T}
    # The collection matcher canonicalizes every finalized subflag. The
    # pairwise matcher first checks predicate counts and reuses isIsomorphic's
    # cache, which is much cheaper for sparse forbidden sets (e.g. Ramsey types).
    isAllowed(F) || return false
    # For large forbidden sets, share the subset traversal across patterns.
    length(p.flags) > 4 && return !isSubFlag(p.flags, F)
    return !any(forbidden -> _generation_forbidden_match(forbidden, F), p.flags)
end

function (p::_GenerationForbidden{T})(F::PartiallyLabeledFlag{T}) where {T}
    return p(labelCanonically(F.F))
end

function _generation_unlabeled_callbacks(
    ::Type{PartiallyLabeledFlag{T}}, property::_GenerationForbidden{T},
    marked::_GenerationForbidden{T},
) where {T}
    return property == marked
end

# Models with other kinds of restrictions retain the existing pruning semantics.
# FlagModel supplies the specialization for supported induced flag algebras.
function _generate_model_flags(T, n, bounds, model; initial_flag=one(T), kwargs...)
    return generateAll(
        T, n, bounds; initial_flag,
        withProperty=F -> isAllowed(model, F),
        withPropertyMarked=F -> isAllowed(model, F), kwargs...,
    )
end

# Unlike canonicalization for non-induced flags, the temporary induced wrapper
# retains isolated vertices: some of them may receive labels later.
_generation_preserve_vertices(F::InducedFlag) = F
_generation_preserve_vertices(F::Flag) = InducedFlag{typeof(F),false}(F)
_generation_unwrap(::Type{T}, F::T) where {T} = F
_generation_unwrap(::Type{T}, F::InducedFlag{T,false}) where {T} = F.F

function _generation_matches_seed(F::PartiallyLabeledFlag, seed::PartiallyLabeledFlag)
    k = seed.n
    if F.n < k
        # Labels are ordered, so even a noncanonical seed must match pointwise.
        return subFlag(F.F, 1:F.n) == subFlag(seed.F, 1:F.n)
    end
    if size(seed) == k
        return subFlag(F.F, 1:k) == seed.F
    end
    # The remaining seed vertices must be UNLABELED in the output. Merely
    # testing that the underlying object contains the seed would overgenerate.
    for extra in combinations((F.n + 1):size(F), size(seed) - k)
        candidate = PartiallyLabeledFlag(subFlag(F.F, vcat(1:k, extra)), k)
        if label(candidate; removeIsolated=false)[1] == seed
            return true
        end
    end
    return false
end

function _generation_labelings!(result, F::PartiallyLabeledFlag, seed, maxLabels)
    F, group, _, _ = label(F; removeIsolated=false)
    _generation_matches_seed(F, seed) || return
    if F.n >= seed.n
        # This removes only the isolated vertices that remain unlabeled.
        push!(result, any(isolatedVertices(F)) ? labelCanonically(F) : F)
    end
    F.n == maxLabels && return

    # Choose one next label per orbit of the pointwise stabilizer of all
    # previous labels. This avoids enumerating all n!/(n-k)! label tuples.
    covered = falses(size(F))
    for v in (F.n + 1):size(F)
        covered[v] && continue
        covered[orbit(group, v)] .= true
        p = collect(1:size(F))
        p[F.n + 1], p[v] = p[v], p[F.n + 1]
        next = PartiallyLabeledFlag(permute(F.F, p), F.n + 1)
        _generation_labelings!(result, next, seed, maxLabels)
    end
    return nothing
end

# Assign the required seed labels before canonicalizing. Most ordered tuples
# fail to induce the seed, so canonicalizing every partial tuple is wasteful.
function _generation_seed_labelings!(result, G, labels, group, seed, maxLabels)
    k = length(labels)
    if k == seed.n
        order = vcat(labels, setdiff(1:size(G), labels))
        F = PartiallyLabeledFlag(permute(G, invperm(order)), k)
        _generation_labelings!(result, F, seed, maxLabels)
        return nothing
    end

    covered = falses(size(G))
    covered[labels] .= true
    prefix = subFlag(seed.F, 1:(k + 1))
    for v in 1:size(G)
        covered[v] && continue
        covered[orbit(group, v)] .= true
        push!(labels, v)
        if subFlag(G, labels) == prefix
            H = k + 1 == seed.n ? group : stabilizer(group, [v])
            _generation_seed_labelings!(result, G, labels, H, seed, maxLabels)
        end
        pop!(labels)
    end
    return nothing
end

function _generate_partially_labeled(
    ::Type{PartiallyLabeledFlag{T}}, maxVertices, maxPredicates, initial_flag, limit, parallel;
    withProperty=_generation_accept_all, withPropertyMarked=_generation_accept_all,
) where {T}
    result = PartiallyLabeledFlag{T}[initial_flag]
    maxVertices <= size(initial_flag) && return result

    seed = label(initial_flag; removeIsolated=false)[1]
    # Different ordered types can have isomorphic underlying seeds. Share the
    # expensive underlying generation; the original seed labels are matched below.
    underlying_seed = labelCanonically(_generation_preserve_vertices(initial_flag.F))
    underlying = generateAll(
        typeof(underlying_seed), maxVertices, maxPredicates[2:end];
        initial_flag=underlying_seed, limit=limit, use_unlabeled=false, parallel=parallel,
        withProperty, withPropertyMarked,
    )
    extensions = filter(G -> size(G) > size(initial_flag), underlying)
    labeled = Vector{Vector{PartiallyLabeledFlag{T}}}(undef, length(extensions))
    _generation_foreach(length(extensions), parallel) do _, j
        G = extensions[j]
        local_result = PartiallyLabeledFlag{T}[]
        # Original seed vertices cannot acquire new labels during extension.
        maxLabels = min(maxPredicates[1], seed.n + size(G) - size(seed))
        F = _generation_unwrap(T, G)
        if seed.n == 0
            _generation_labelings!(local_result, PartiallyLabeledFlag(F, 0), seed, maxLabels)
        else
            group = label(F; removeIsolated=false)[3]
            _generation_seed_labelings!(local_result, F, Int[], group, seed, maxLabels)
        end
        labeled[j] = local_result
    end
    for flags in labeled
        append!(result, flags)
    end
    # Preserve the seed as the first entry and the underlying vertex layers.
    unique!(result)
    # Model samplers expose these vectors as well as coefficient dictionaries.
    # Match the incremental generator's ordering, independently of scheduling.
    if withProperty isa _GenerationForbidden
        sort!(@view(result[2:end]); by=F -> (size(F), hash(F)))
    end
    return result
end
