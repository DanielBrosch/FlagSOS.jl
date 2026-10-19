# Use task-owned buffers, never buffers indexed by threadid(): Julia tasks can
# migrate and the default thread pool need not start at thread ID 1.
function _generation_workers(n::Int, parallel::Bool)
    return parallel && n >= 16 ? min(n, Threads.nthreads()) : 1
end

function _generation_foreach(f, n::Int, parallel::Bool)
    workers = _generation_workers(n, parallel)
    if workers == 1
        for i in 1:n
            f(1, i)
        end
        return nothing
    end

    # Amortize the shared atomic over batches, while leaving enough batches to
    # balance expensive canonicalizations across large thread pools.
    batch = clamp(cld(n, 16 * workers), 1, 32)
    next = Threads.Atomic{Int}(1)
    @sync for worker in 1:workers
        Threads.@spawn begin
            while true
                first = Threads.atomic_add!(next, batch)
                first > n && break
                for i in first:min(first + batch - 1, n)
                    f(worker, i)
                end
            end
        end
    end
    return nothing
end

struct _GenerationSeen
    buckets::Vector{Set{UInt}}
    locks::Vector{ReentrantLock}
end

function _GenerationSeen(parallel::Bool)
    workers = parallel ? Threads.nthreads() : 1
    shards = workers == 1 ? 1 : nextpow(2, 8 * workers)
    return _GenerationSeen([Set{UInt}() for _ in 1:shards], [ReentrantLock() for _ in 1:shards])
end

function _generation_claim!(seen::_GenerationSeen, F)
    h = hash(F)
    bucket = Int(h & UInt(length(seen.buckets) - 1)) + 1
    entries = seen.buckets[bucket]
    if length(seen.buckets) == 1
        h in entries && return false
        push!(entries, h)
        return true
    end
    # No canonicalization, allocation of children, or queue operations under
    # this lock. Different hash shards can be updated independently.
    lock(seen.locks[bucket]) do
        h in entries && return false
        push!(entries, h)
        return true
    end
end

function _generation_extend_vertex!(
    output, pending, f::T, i, maxPredicates, withProperty, seen
) where {T}
    newF = permute(f, 1:i)
    withProperty(newF) && push!(output, newF)
    currentEdges = countEdges(newF)
    if length(maxPredicates) < length(currentEdges) && (
        maxPredicates[end] isa Int &&
        maxPredicates[end] <= sum(sum.(currentEdges[length(maxPredicates):end]))
    )
        return nothing
    end

    fixed = allowMultiEdges(T) ? Vector{Int}[] : [collect(1:(i - 1))]
    uP::Vector{Vector{predicateType(T)}} = findUnknownPredicates(newF, fixed, maxPredicates)
    uP2 = findUnknownGenerationPredicates(newF, fixed, maxPredicates)
    if uP2 !== nothing
        uP = vcat(uP, uP2)
    end
    length(uP) == 1 && isempty(uP[1]) && return nothing
    for j in eachindex(maxPredicates)
        currentEdges[j] == maxPredicates[j] && empty!(uP[j])
    end
    FMarked = EdgeMarkedFlag{T}(newF, uP)
    for (F, _) in allWaysToAddOneMarked(FMarked; removeEarlierMarked=true)
        if allowMultiEdges(T)
            F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
        end
        if hasAtMostEdges(F.F, maxPredicates) && _generation_claim!(seen, F)
            push!(pending, F)
        end
    end
    return nothing
end

function _generate_vertex_layer(
    previous::Vector{T}, i, maxPredicates, withProperty, withPropertyMarked, parallel
) where {T}
    M = EdgeMarkedFlag{T,predicateType(T)}
    workers = parallel ? Threads.nthreads() : 1
    output = [Set{T}() for _ in 1:workers]
    initial = [M[] for _ in 1:workers]
    seen = _GenerationSeen(parallel)
    _generation_foreach(length(previous), parallel) do worker, j
        _generation_extend_vertex!(
            output[worker], initial[worker], previous[j], i, maxPredicates, withProperty, seen
        )
    end
    frontier = reduce(vcat, initial)

    # Bulk scheduling avoids a contended Channel and its per-state termination
    # counter. @sync also propagates callback errors without stranding consumers.
    while !isempty(frontier)
        frontier = _generation_process_frontier!(
            output, frontier, maxPredicates, withProperty, withPropertyMarked, seen, parallel
        )
    end

    raw = collect(reduce(union!, output))
    result = Vector{T}(undef, length(raw))
    _generation_foreach(length(raw), parallel) do _, j
        result[j] = labelCanonically(raw[j])
    end
    # Discovery order depends on scheduling. Order canonical representatives
    # consistently so downstream vector-valued APIs agree across uncached runs.
    return sort!(unique!(result); by=hash)
end

function _generation_process_frontier!(
    output, frontier::Vector{M}, maxPredicates, withProperty, withPropertyMarked, seen, parallel
) where {M}
    T = fieldtype(M, :F)
    pending = [M[] for _ in eachindex(output)]
    _generation_foreach(length(frontier), parallel) do worker, j
        FMarked = frontier[j]
        withProperty(FMarked.F) && push!(output[worker], FMarked.F)
        for F in process_edgeMarkedFlags(FMarked, maxPredicates, withPropertyMarked, T)
            _generation_claim!(seen, F) && push!(pending[worker], F)
        end
    end
    return reduce(vcat, pending)
end
