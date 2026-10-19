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
    ::Type{PartiallyLabeledFlag{T}}, maxVertices, maxPredicates, initial_flag, limit
) where {T}
    result = PartiallyLabeledFlag{T}[initial_flag]
    maxVertices <= size(initial_flag) && return result

    seed = label(initial_flag; removeIsolated=false)[1]
    underlying_seed = _generation_preserve_vertices(initial_flag.F)
    underlying = generateAll(
        typeof(underlying_seed), maxVertices, maxPredicates[2:end];
        initial_flag=underlying_seed, limit=limit, use_unlabeled=false,
    )
    for G in underlying
        size(G) <= size(initial_flag) && continue
        # Original seed vertices cannot acquire new labels during extension.
        maxLabels = min(maxPredicates[1], seed.n + size(G) - size(seed))
        F = _generation_unwrap(T, G)
        if seed.n == 0
            _generation_labelings!(result, PartiallyLabeledFlag(F, 0), seed, maxLabels)
        else
            group = label(F; removeIsolated=false)[3]
            _generation_seed_labelings!(result, F, Int[], group, seed, maxLabels)
        end
    end
    # Preserve the seed as the first entry and the underlying vertex layers.
    return unique!(result)
end
