export generateAll

include("SchreierSims.jl")

using DataStructures
using Base.Threads
using Memoization

include("ParallelGeneration.jl")

# Cells occupy consecutive positions in `vertices`. Only cell starts have a
# nonzero entry in `cell_end`; their positions stay valid when another cell splits.
mutable struct _LabelPartition
    vertices::Vector{Int}
    cell_end::Vector{Int}
    ncells::Int
end

function _LabelPartition(colors::Vector{Int})
    vertices = sortperm(colors)
    cell_end = zeros(Int, length(colors))
    ncells = 0
    first = 1
    while first <= length(colors)
        last = first
        while last < length(colors) && colors[vertices[last + 1]] == colors[vertices[first]]
            last += 1
        end
        cell_end[first] = last
        ncells += 1
        first = last + 1
    end
    return _LabelPartition(vertices, cell_end, ncells)
end

Base.copy(p::_LabelPartition) = _LabelPartition(copy(p.vertices), copy(p.cell_end), p.ncells)

struct _LabelWorkspace
    active::BitVector
    splitter::BitVector
    values::Vector{UInt}
end

_LabelWorkspace(n::Int) = _LabelWorkspace(falses(n), falses(n), zeros(UInt, n))

function _individualize!(p::_LabelPartition, cell::Int, vertex::Int)
    last = p.cell_end[cell]
    @assert cell < last
    pos = cell
    while p.vertices[pos] != vertex
        pos += 1
    end
    p.vertices[cell], p.vertices[pos] = p.vertices[pos], p.vertices[cell]
    p.cell_end[cell] = cell
    p.cell_end[cell + 1] = last
    p.ncells += 1
    return nothing
end

function _refine!(p::_LabelPartition, F, work::_LabelWorkspace, individualized::Int=0)
    n = length(p.vertices)
    active, splitter, values = work.active, work.splitter, work.values
    fill!(active, false)
    if individualized == 0
        # Every initial color class can distinguish vertices in another class.
        cell = 1
        while cell <= n
            active[cell] = true
            cell = p.cell_end[cell] + 1
        end
    else
        # The parent is already refined. Both parts of the individualized cell
        # are new splitters; neither can be inferred from the other for an oracle.
        active[individualized] = true
        active[individualized + 1] = true
    end

    # A hash of the ordered refinement trace replaces the dense quotient matrix.
    # Hash collisions here only weaken pruning, since leaves are compared below.
    invariant = hash(p.ncells)
    while p.ncells < n
        split = findfirst(active)
        split === nothing && break
        active[split] = false
        fill!(splitter, false)
        for pos in split:p.cell_end[split]
            splitter[p.vertices[pos]] = true
        end
        invariant = hash((split, p.cell_end[split] - split + 1), invariant)

        cell = 1
        while cell <= n
            last = p.cell_end[cell]
            if cell == last
                cell += 1
                continue
            end
            for pos in cell:last
                vertex = p.vertices[pos]
                values[vertex] = distinguish(F, vertex, splitter)
            end
            sort!(@view(p.vertices[cell:last]); by=v -> values[v])
            splits = values[p.vertices[cell]] != values[p.vertices[last]]
            first = cell
            while first <= last
                stop = first
                value = values[p.vertices[first]]
                while stop < last && values[p.vertices[stop + 1]] == value
                    stop += 1
                end
                p.cell_end[first] = stop
                invariant = hash((first, stop - first + 1, value), invariant)
                if splits
                    # The graph-specific "all but the largest part" shortcut
                    # requires additivity, which `distinguish` does not promise.
                    active[first] = true
                    first != cell && (p.ncells += 1)
                end
                first = stop + 1
            end
            cell = last + 1
        end
    end
    return hash(p.ncells, invariant)
end

# Retain the coloring-based helper. Colors need not be consecutive; their order
# is preserved. A nonzero vertex individualizes a nonsingleton cell first.
function refine!(coloring::Vector{Int}, F, vertex::Int)::Vector{UInt}
    length(coloring) == size(F) || throw(DimensionMismatch("one color is required per vertex"))
    p = _LabelPartition(coloring)
    cell = 0
    if vertex != 0
        checkbounds(coloring, vertex)
        cell = 1
        while !(vertex in @view(p.vertices[cell:p.cell_end[cell]]))
            cell = p.cell_end[cell] + 1
        end
        cell == p.cell_end[cell] && throw(ArgumentError("cannot individualize a singleton cell"))
        _individualize!(p, cell, vertex)
    end
    # This entry point also accepts unrefined input, so activate every cell.
    invariant = _refine!(p, F, _LabelWorkspace(length(coloring)))
    cell, color = 1, 1
    while cell <= length(coloring)
        for pos in cell:p.cell_end[cell]
            coloring[p.vertices[pos]] = color
        end
        color += 1
        cell = p.cell_end[cell] + 1
    end
    return p.ncells == length(coloring) ?
           UInt[invariant, hash(permute(F, coloring))] : UInt[invariant]
end

mutable struct _LabelSearch{T,K,C}
    F::T
    canonical_key::C
    best_key::K
    first_flag::T
    best_flag::T
    first_inverse::Vector{Int}
    best_inverse::Vector{Int}
    first_invariant::Vector{UInt}
    best_invariant::Vector{UInt}
    invariant::Vector{UInt}
    branch::Vector{Int}
    covered::Vector{Vector{Int}}
    group::Group
    work::_LabelWorkspace
    prune::Bool
end

# Compare only the shared prefix: an unfinished branch can still improve a leaf
# when its trace extends that leaf's trace.
function _compare_prefix(a::Vector{UInt}, b::Vector{UInt})
    for i in 1:min(length(a), length(b))
        a[i] < b[i] && return -1
        a[i] > b[i] && return 1
    end
    return 0
end

function _automorphism_cutoff!(search::_LabelSearch)
    for depth in eachindex(search.branch)
        H = stabilizer!(search.group, search.branch[1:(depth - 1)])
        orbit!(H, search.covered[depth])
        search.branch[depth] in search.covered[depth] && return depth
    end
    return 0
end

function _record_leaf!(search::_LabelSearch, partition::_LabelPartition)
    permutation = invperm(partition.vertices)
    candidate = permute(search.F, permutation)
    key = search.canonical_key(candidate)
    if isempty(search.first_inverse)
        search.first_flag = candidate
        search.best_flag = candidate
        search.best_key = key
        append!(search.first_inverse, partition.vertices)
        append!(search.best_inverse, partition.vertices)
        append!(search.first_invariant, search.invariant)
        append!(search.best_invariant, search.invariant)
        return 0
    end

    changed = false
    if candidate == search.first_flag
        changed = addGen!(search.group, search.first_inverse[permutation])
    end
    if candidate == search.best_flag && search.best_inverse != search.first_inverse
        changed |= addGen!(search.group, search.best_inverse[permutation])
    end

    same_trace = search.invariant == search.best_invariant
    if same_trace && isequal(key, search.best_key) && candidate != search.best_flag
        throw(ArgumentError(
            "canonicalKey ties for unequal labeled objects; supply a canonicalKey " *
            "that distinguishes them (for example an exact ordered encoding)",
        ))
    end
    if search.invariant > search.best_invariant ||
       (same_trace && isless(search.best_key, key))
        search.best_flag = candidate
        search.best_key = key
        search.best_inverse .= partition.vertices
        resize!(search.best_invariant, length(search.invariant))
        search.best_invariant .= search.invariant
    end
    return changed && search.prune ? _automorphism_cutoff!(search) : 0
end

function _target_cell(p::_LabelPartition)
    target, smallest = 0, typemax(Int)
    cell = 1
    while cell <= length(p.vertices)
        len = p.cell_end[cell] - cell + 1
        if 1 < len < smallest
            target, smallest = cell, len
            len == 2 && break
        end
        cell = p.cell_end[cell] + 1
    end
    return target
end

function _search_label!(search::_LabelSearch, partition::_LabelPartition)::Int
    n = length(partition.vertices)
    partition.ncells == n && return _record_leaf!(search, partition)

    # Keep the first leaf's path available to discover the full automorphism
    # group, as well as every branch that can improve the canonical leaf.
    if search.prune && !isempty(search.first_inverse) &&
       _compare_prefix(search.invariant, search.first_invariant) != 0 &&
       _compare_prefix(search.invariant, search.best_invariant) < 0
        return 0
    end

    cell = _target_cell(partition)
    depth = length(search.branch)
    covered = Int[]
    push!(search.covered, covered)
    cutoff = 0
    for pos in cell:partition.cell_end[cell]
        vertex = partition.vertices[pos]
        search.prune && vertex in covered && continue
        child = copy(partition)
        _individualize!(child, cell, vertex)
        push!(search.branch, vertex)
        push!(search.invariant, _refine!(child, search.F, search.work, cell))
        cutoff = _search_label!(search, child)
        pop!(search.invariant)
        pop!(search.branch)
        # Each frame owns its stack entries, including during a backjump.
        cutoff != 0 && cutoff <= depth && break
        cutoff = 0
        if search.prune
            push!(covered, vertex)
            H = stabilizer!(search.group, search.branch)
            orbit!(H, covered)
        end
    end
    pop!(search.covered)
    return cutoff
end

"""
    label(F; prune=true, removeIsolated=true, canonicalKey=hash)

Return `(canonical, canonical_group, original_group, permutation)`, where
`canonical == permute(F, permutation)` and the two groups act on the canonical
and original vertex sets, respectively. `permutation[v]` is the new label of `v`.
If isolated vertices are removed, all four results refer to the reduced object.

The individualization/refinement search uses only `size`, `vertexColor`,
`distinguish`, `permute`, and equality, plus `isolatedVertices` and `subFlag` when
removing isolated vertices. Vertex colors must be ordered integers preserved by
isomorphisms. The `UInt` returned by `distinguish(F, v, W)` must be invariant under
simultaneous relabeling of `F`, `v`, and `W`; it need not be additive or complete.

Refinement traces order the search leaves; `canonicalKey` breaks ties. Its values
must have a total order and agree for equal labeled objects. The default uses
`hash`; a tie between unequal objects raises an error instead of silently making
the result depend on input labels. An exact ordered encoding can be supplied for
objects with deliberately weak hashes. Canonical representatives may change with
the implementation or Julia's hashing, so they are not a persistent file format.

Set `prune=false` to explore the complete refinement tree, retaining the same
canonicalization rule and automorphism computation. Search buffers belong to each
call, so independent calls can run concurrently.
"""
function label(F; prune=true, removeIsolated=true, canonicalKey=hash)
    n = size(F)
    if n > 0 && removeIsolated
        isolated = isolatedVertices(F)
        if any(isolated)
            return label(subFlag(F, .!isolated); prune, removeIsolated, canonicalKey)
        end
    end
    n == 0 && return F, Group(0), Group(0), Int[]

    partition = _LabelPartition(Int[vertexColor(F, v) for v in 1:n])
    work = _LabelWorkspace(n)
    invariant = _refine!(partition, F, work)
    if partition.ncells == n
        permutation = invperm(partition.vertices)
        return permute(F, permutation), Group(n), Group(n), permutation
    end
    search = _LabelSearch(
        F, canonicalKey, canonicalKey(F), F, F, Int[], Int[], UInt[], UInt[],
        UInt[invariant], Int[], Vector{Int}[], Group(n), work, prune,
    )
    _search_label!(search, partition)
    permutation = invperm(search.best_inverse)
    canonical_group = permute!(deepcopy(search.group), permutation)
    return search.best_flag, canonical_group, search.group, permutation
end


_generation_accept_all(F) = true
_can_generate_unlabeled(::Type, initial_flag, maxPredicates) = false
_generation_unlabeled_callbacks(::Type, property, marked) =
    property === _generation_accept_all && marked === _generation_accept_all

function generateAll(
    ::Type{F},
    maxVertices::Int,
    maxEdges::Int;
    withProperty=_generation_accept_all,
    initial_flag=one(F),
    kwargs...,
) where {F}
    return generateAll(
        F, maxVertices, [maxEdges]; withProperty=withProperty, initial_flag=initial_flag,
        kwargs...,
    )
end

#TODO: Quite a bit slower than nauty/traces, how are they doing it?
# function generateAll(
#     ::Type{T},
#     maxVertices::Int,
#     maxPredicates::Vector;
#     withProperty=(F::T) -> true,
#     # withPropertyMarked=(F::EdgeMarkedFlag{T, predicateType(T)}) -> true,
#     withPropertyMarked=(F) -> true,
#     # withInducedProperty=(F::T) -> true,
# ) where {T}
#     generatedGraphs = Vector{T}[Vector([one(T)])]
#     for i in 1:maxVertices
#         @show (i, maxVertices)
#         nextGraphs = T[]

#         pq = PriorityQueue{EdgeMarkedFlag{T,predicateType(T)},Vector{Int}}()
#         # pq = PriorityQueue{EdgeMarkedFlag{T,predicateType(T)},Any}()

#         for f in generatedGraphs[i]
#             newF = permute(f, 1:i)
#             # if newF == nothing 
#             #     continue 
#             # end

#             # @show newF
#             # @show size(newF)
#             # if withInducedProperty(newF) && 
#             if withProperty(newF)
#                 push!(nextGraphs, newF)
#             end
#             currentEdges = countEdges(newF)
#             # @show currentEdges
#             # @show length(currentEdges)
#             # @show currentEdges[length(maxPredicates):end]
#             # @show sum(currentEdges[length(maxPredicates):end])
#             # @show maxPredicates

#             if length(maxPredicates) < length(currentEdges) && (
#                 maxPredicates[end] isa Int &&
#                 maxPredicates[end] <= sum(sum.(currentEdges[length(maxPredicates):end]))
#             )
#                 continue
#             end

#             fixed = allowMultiEdges(T) ? Vector{Int}[] : [collect(1:(i - 1))]
#             uP::Vector{Vector{predicateType(T)}} = findUnknownPredicates(
#                 newF, fixed, maxPredicates
#             )
#             # @show uP
#             uP2 = findUnknownGenerationPredicates(newF, fixed, maxPredicates)
#             if uP2 !== nothing
#                 uP = vcat(uP, uP2)
#             end

#             if length(uP) == 1 && length(uP[1]) == 0
#                 continue
#             end

#             for i in 1:length(maxPredicates)
#                 if currentEdges[i] == maxPredicates[i]
#                     empty!(uP[i])
#                 end
#             end
#             # @show uP
#             uP = Vector{Vector{predicateType(T)}}(uP)
#             FMarked = EdgeMarkedFlag{T}(newF, uP)
#             for (F, _) in allWaysToAddOneMarked(FMarked)
#                 if allowMultiEdges(T)
#                     F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
#                 end
#                 # @show F
#                 cP = countEdges(F)[1:(end - 1)]
#                 # @show cP
#                 # @assert length(maxPredicates) == length(cP)
#                 if length(maxPredicates) == length(cP) && all(cP .<= maxPredicates)
#                     pq[F] = cP
#                 elseif all(
#                         cP[1:(length(maxPredicates) - 1)] .<= maxPredicates[1:(end - 1)]
#                     ) &&
#                     maxPredicates[end] isa Union{Int,Vector{Int}} &&
#                     sum(sum.(cP[length(maxPredicates):end])) <= sum(maxPredicates[end])
#                     pq[F] = cP
#                 end
#             end
#         end

#         t = time()

#         while !isempty(pq)
#             if time() - t > 1
#                 @show length(pq)
#                 t = time()
#             end
#             FMarked = dequeue!(pq)
#             # @show countEdges(FMarked)
#             # @show (length(pq), sum(countEdges(FMarked.F)))
#             # @show FMarked
#             # if withInducedProperty(FMarked.F) && withProperty(FMarked.F)
#             if withProperty(FMarked.F)
#                 # continue
#                 push!(nextGraphs, FMarked.F)
#             end
#             cP = countEdges(FMarked.F)
#             if length(maxPredicates) == length(cP) && all(cP .== maxPredicates)
#                 continue
#             elseif all(cP[1:(length(maxPredicates) - 1)] .== maxPredicates[1:(end - 1)]) &&
#                 sum(cP[length(maxPredicates):end]) == maxPredicates[end]
#                 continue
#             end
#             # if !all(countEdges(FMarked.F) .== maxPredicates)
#             #TODO: this lets graphs appear many times by adding edges in different orders! Solution (?): when adding a marked edge, delete all "earlier" marked edges
#             for (F, _) in allWaysToAddOneMarked(FMarked; removeEarlierMarked=true)
#                 # for (F, _) in allWaysToAddOneMarked(FMarked; removeEarlierMarked = false)
#                 if allowMultiEdges(T)
#                     # @show FMarked.marked
#                     # @show F.marked
#                     if T <: ProductFlag
#                         for (i, FT) in enumerate(fieldtypes(fieldtypes(T)[1]))
#                             if allowMultiEdges(FT)
#                                 union!(F.marked, [e for e in FMarked.marked if e[1] == i])
#                             end
#                         end
#                     else
#                         F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
#                     end
#                 end
#                 # @assert sum(countEdges(FMarked.F)) < sum(countEdges(F.F))
#                 # if !withProperty(F.F)
#                 if !withPropertyMarked(F)
#                     continue
#                 end

#                 cP = countEdges(F)[1:(end - 1)]
#                 # if all(cP .<= maxPredicates)
#                 #     pq[F] = cP
#                 # end
#                 # @show maxPredicates
#                 # @show cP

#                 # F2 = labelCanonically(F) # not worth? ALREADY LABELED 
#                 # @assert F2 == F # always... because the new vertex has to be in same position, and others are already canonically labeled. There must be a better way??? Cant be right..., check small graphs
#                 # F = F2

#                 cpOrder = countEdges(F)
#                 cpOrder[end] *= -1

#                 if length(maxPredicates) == length(cP) && all(cP .<= maxPredicates)
#                     # pq[F] = cP
#                     pq[F] = cpOrder
#                 elseif maxPredicates[end] isa Int &&
#                     all(cP[1:(length(maxPredicates) - 1)] .<= maxPredicates[1:(end - 1)]) &&
#                     sum(sum.(cP[length(maxPredicates):end])) <= maxPredicates[end]
#                     # pq[F] = cP
#                     pq[F] = cpOrder
#                 end
#             end
#             # end
#         end

#         @show length(nextGraphs)
#         unique!(nextGraphs)
#         @show length(nextGraphs)
#         k = length(nextGraphs)
#         res = T[]
#         t = time()
#         for (i, G) in enumerate(nextGraphs)
#             if time() - t > 1
#                 @show i, k
#                 t = time()
#             end
#             push!(res, labelCanonically(G))
#         end
#         unique!(res)

#         push!(generatedGraphs, res)
#         # push!(generatedGraphs, unique(labelCanonically.(nextGraphs)))
#     end
#     return unique(vcat(generatedGraphs...))
# end

# function process_edgeMarkedFlags_old(
#     flags,
#     nextGraphs,
#     withProperty,
#     maxPredicates,
#     withPropertyMarked,
#     T,
#     doneFlags,
#     doneFlags_lock,
#     noRunning,
# )
#     # if time() - t > 1 
#     #     @show length(pq)
#     #     t = time()
#     # end
#     # @show "starting processing"
#     # @show isready(flags)
#     # while true

#     # while true #isready(flags) #|| noRunning[] > 0
#     # while isready(flags) || noRunning[] > 0
#     # while true
#     # @assert noRunning[] > 0

#     if noRunning[] == 0 && !isready(flags)
#         return nothing
#     end
#     for FMarked in flags
#         # try
#         # FMarked = take!(flags)

#         # if isready(flags)
#         # else
#         #     sleep(0.001)
#         #     continue 
#         # end 

#         # FMarked = lock(doneFlags_lock) do 
#         #     if isempty(flags)
#         #         return nothing 
#         #     end

#         #     # if time() - t > 1
#         #     #     @show length(pq)
#         #     #     t = time()
#         #     # end
#         #     return dequeue!(flags)
#         # end
#         # if FMarked === nothing 
#         #     return 
#         # end

#         # for FMarked in flags
#         # wait(flags)
#         # try 
#         #     FMarked = take!(flags)
#         # catch 
#         #     return 
#         # end
#         # noRunning[] += 1
#         Threads.atomic_add!(noRunning, 1)
#         # @show noRunning[]
#         # @show FMarked

#         # FMarked = dequeue!(pq)
#         # @show countEdges(FMarked)
#         # @show (length(pq), sum(countEdges(FMarked.F)))
#         # @show FMarked
#         # if withInducedProperty(FMarked.F) && withProperty(FMarked.F)
#         if withProperty(FMarked.F)
#             # continue
#             # push!(nextGraphs, FMarked.F)
#             put!(nextGraphs, FMarked.F)
#         end
#         cP = countEdges(FMarked.F)
#         if length(maxPredicates) == length(cP) && all(cP .== maxPredicates)
#             # noRunning[] -= 1
#             Threads.atomic_add!(noRunning, -1)
#             continue
#         elseif all(cP[1:(length(maxPredicates) - 1)] .== maxPredicates[1:(end - 1)]) &&
#             sum(cP[length(maxPredicates):end]) == maxPredicates[end]
#             # noRunning[] -= 1

#             Threads.atomic_add!(noRunning, -1)
#             continue
#         end
#         # if !all(countEdges(FMarked.F) .== maxPredicates)
#         #TODO: this lets graphs appear many times by adding edges in different orders! Solution (?): when adding a marked edge, delete all "earlier" marked edges
#         for (F, _) in allWaysToAddOneMarked(FMarked; removeEarlierMarked=true)
#             if allowMultiEdges(T)
#                 # @show FMarked.marked
#                 # @show F.marked
#                 if T <: ProductFlag
#                     for (i, FT) in enumerate(fieldtypes(fieldtypes(T)[1]))
#                         if allowMultiEdges(FT)
#                             union!(F.marked, [e for e in FMarked.marked if e.i == i])
#                         end
#                     end
#                 else
#                     F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
#                 end
#             end
#             # @assert sum(countEdges(FMarked.F)) < sum(countEdges(F.F))
#             # if !withProperty(F.F)
#             if !withPropertyMarked(F)
#                 continue
#             end

#             cP = countEdges(F)[1:(end - 1)]
#             # if all(cP .<= maxPredicates)
#             #     pq[F] = cP
#             # end
#             # @show maxPredicates
#             # @show cP

#             # F2 = labelCanonically(F) # not worth? ALREADY LABELED 
#             # @assert F2 == F # always... because the new vertex has to be in same position, and others are already canonically labeled. There must be a better way??? Cant be right..., check small graphs
#             # F = F2

#             if hasAtMostEdges(F.F, maxPredicates)
#                 addF = false
#                 @lock doneFlags_lock if !(F in doneFlags)
#                     push!(doneFlags, F)
#                     addF = true
#                 end
#                 if addF
#                     !isopen(flags) && return nothing
#                     put!(flags, F)
#                 end
#             end

#             # cpOrder = countEdges(F)
#             # cpOrder[end] *= -1

#             # if length(maxPredicates) == length(cP) && all(cP .<= maxPredicates)
#             #     # pq[F] = cP
#             #     # pq[F] = cpOrder
#             #     # @info "putting..."
#             #     addF = false
#             #     @lock doneFlags_lock if !(F in doneFlags)
#             #         push!(doneFlags, F)
#             #         addF = true
#             #     end
#             #     if addF
#             #         !isopen(flags) && return nothing
#             #         put!(flags, F)
#             #     end
#             #     # put!(flags, F)
#             # elseif maxPredicates[end] isa Int &&
#             #        all(cP[1:(length(maxPredicates)-1)] .<= maxPredicates[1:(end-1)]) &&
#             #        sum(sum.(cP[length(maxPredicates):end])) <= maxPredicates[end]
#             #     # pq[F] = cP
#             #     # pq[F] = cpOrder
#             #     # @info "putting..."
#             #     # put!(flags, F)
#             #     # if !(F in doneFlags)
#             #     addF = false
#             #     @lock doneFlags_lock if !(F in doneFlags)
#             #         push!(doneFlags, F)
#             #         addF = true
#             #     end
#             #     addF && put!(flags, F)
#             #     # put!(flags, F)
#             #     # end
#             # end
#         end
#         # noRunning[] -= 1

#         Threads.atomic_add!(noRunning, -1)
#         # catch
#         #     sleep(0.01)
#         #     continue
#         # end
#     end
#     # @info "thread done"
# end

# function generateAll_old(
#     ::Type{T},
#     maxVertices::Int,
#     maxPredicates::Vector;
#     withProperty=(F::T) -> true,
#     # withPropertyMarked=(F::EdgeMarkedFlag{T, predicateType(T)}) -> true,
#     withPropertyMarked=(F) -> true,
#     # withInducedProperty=(F::T) -> true,
#     limit::Int=100_000,
#     initial_flag=one(T),
# ) where {T}
#     generatedGraphs = Vector{T}[Vector([initial_flag])]
#     @show maxPredicates
#     for i in (size(initial_flag) + 1):maxVertices
#         @show (i, maxVertices)
#         # nextGraphs = T[]
#         nextGraphs = Channel{T}(Inf)

#         pq = Channel{EdgeMarkedFlag{T,predicateType(T)}}(Inf)
#         # pq = PriorityQueue{EdgeMarkedFlag{T,predicateType(T)},Vector{Int}}()
#         # pq = PriorityQueue{EdgeMarkedFlag{T,predicateType(T)},Any}()

#         doneFlags = Set{EdgeMarkedFlag{T,predicateType(T)}}()
#         # doneFlags_lock = ReentrantLock()
#         doneFlags_lock = Base.Threads.SpinLock()

#         for f in generatedGraphs[i - size(initial_flag)]
#             newF = permute(f, 1:i)
#             # if newF == nothing 
#             #     continue 
#             # end

#             # @show newF
#             # @show size(newF)
#             # if withInducedProperty(newF) && 
#             if withProperty(newF)
#                 put!(nextGraphs, newF)
#             end
#             currentEdges = countEdges(newF)
#             # @show currentEdges
#             # @show length(currentEdges)
#             # @show currentEdges[length(maxPredicates):end]
#             # @show sum(currentEdges[length(maxPredicates):end])
#             # @show maxPredicates

#             if length(maxPredicates) < length(currentEdges) && (
#                 maxPredicates[end] isa Int &&
#                 maxPredicates[end] <= sum(sum.(currentEdges[length(maxPredicates):end]))
#             )
#                 continue
#             end

#             fixed = allowMultiEdges(T) ? Vector{Int}[] : [collect(1:(i - 1))]
#             uP::Vector{Vector{predicateType(T)}} = findUnknownPredicates(
#                 newF, fixed, maxPredicates
#             )
#             # @show uP
#             uP2 = findUnknownGenerationPredicates(newF, fixed, maxPredicates)
#             if uP2 !== nothing
#                 uP = vcat(uP, uP2)
#             end

#             if length(uP) == 1 && length(uP[1]) == 0
#                 continue
#             end

#             for i in 1:length(maxPredicates)
#                 if currentEdges[i] == maxPredicates[i]
#                     empty!(uP[i])
#                 end
#             end
#             # @show uP
#             uP = Vector{Vector{predicateType(T)}}(uP)
#             FMarked = EdgeMarkedFlag{T}(newF, uP)
#             for (F, _) in allWaysToAddOneMarked(FMarked; removeEarlierMarked=true)
#                 if allowMultiEdges(T)
#                     F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
#                 end
#                 # @show F
#                 # cP = countEdges(F)[1:(end - 1)]
#                 # @show cP, maxPredicates
#                 # @assert length(maxPredicates) == length(cP)
#                 # if length(maxPredicates) == length(cP) && all(cP .<= maxPredicates)
#                 #     # pq[F] = cP
#                 #     if !(F in doneFlags)
#                 #         @lock doneFlags_lock push!(doneFlags, F)
#                 #         put!(pq, F)
#                 #     end
#                 #     # @show "putting $F"
#                 # elseif all(
#                 #         cP[1:(length(maxPredicates) - 1)] .<= maxPredicates[1:(end - 1)]
#                 #     ) &&
#                 #     maxPredicates[end] isa Union{Int,Vector{Int}} &&
#                 #     sum(sum.(cP[length(maxPredicates):end])) <= sum(maxPredicates[end])
#                 #     # pq[F] = cP
#                 #     # if !(F in doneFlags)
#                 #     if !(F in doneFlags)
#                 #         @lock doneFlags_lock push!(doneFlags, F)
#                 #         put!(pq, F)
#                 #     end
#                 #     # put!(pq, F)
#                 #     # end
#                 #     # @show "putting $F"
#                 # end
#                 if hasAtMostEdges(F.F, maxPredicates)
#                     if !(F in doneFlags)
#                         @lock doneFlags_lock push!(doneFlags, F)
#                         put!(pq, F)
#                     end
#                 end
#             end
#         end

#         t = time()

#         tasks = []
#         # @show nextGraphs
#         # @show pq

#         # if length(pq) > 0 
#         if isready(pq)
#             noRunning = Threads.Atomic{Int}(0)
#             noRunningNow = 1
#             maxModels = 0
#             # @show noRunning[], Base.n_avail(pq), islocked(doneFlags_lock)
#             # t = @async process_edgeMarkedFlags(pq, nextGraphs, withProperty, maxPredicates, withPropertyMarked, T, doneFlags, doneFlags_lock, noRunning)
#             # push!(tasks, t)
#             # sleep(0.01)
#             for _ in 1:(Threads.nthreads() - 1)
#                 t = Threads.@spawn process_edgeMarkedFlags(
#                     pq,
#                     nextGraphs,
#                     withProperty,
#                     maxPredicates,
#                     withPropertyMarked,
#                     T,
#                     doneFlags,
#                     doneFlags_lock,
#                     noRunning,
#                 )
#                 errormonitor(t)
#                 push!(tasks, t)
#             end
#             # @show tasks
#             while isready(pq) || noRunningNow > 0
#                 noRunningNow = noRunning[]
#                 noModels = Base.n_avail(pq)
#                 if noModels > maxModels
#                     maxModels = noModels
#                 end
#                 if maxModels > limit
#                     close(pq)
#                     return :limit
#                 end
#                 print(
#                     "\r$(noRunningNow) active threads, \t$(noModels) models left,\t $maxModels max models\t\t\t",
#                 )
#                 sleep(0.1)
#             end
#             println()
#             # @show noRunning[]
#             close(pq)
#             # @info "closed"
#             # @show noRunning[]

#             wait.(tasks)
#         end

#         close(nextGraphs)
#         nextGraphs = collect(nextGraphs)

#         # while !isempty(pq)

#         #     # end
#         # end

#         # @show length(nextGraphs)
#         unique!(nextGraphs)
#         @show length(nextGraphs)
#         k = length(nextGraphs)
#         res = T[]
#         t = time()
#         for (i, G) in enumerate(nextGraphs)
#             if time() - t > 1
#                 @show i, k
#                 t = time()
#             end
#             push!(res, labelCanonically(G))
#         end
#         unique!(res)

#         push!(generatedGraphs, res)
#         # push!(generatedGraphs, unique(labelCanonically.(nextGraphs)))
#     end
#     return unique(vcat(generatedGraphs...))
# end

##

function process_edgeMarkedFlags(
    FMarked,
    # flags,
    # nextGraphs,
    # withProperty,
    maxPredicates,
    withPropertyMarked,
    T,
    # doneFlags,
    # doneFlags_lock,
)
    newFlags = Set{EdgeMarkedFlag{T,predicateType(T)}}()
    cP = countEdges(FMarked.F)
    if length(maxPredicates) == length(cP) && all(cP .== maxPredicates)
        return newFlags
    elseif all(cP[1:(length(maxPredicates) - 1)] .== maxPredicates[1:(end - 1)]) &&
        sum(cP[length(maxPredicates):end]) == maxPredicates[end]
        return newFlags
    end
    #TODO: this lets graphs appear many times by adding edges in different orders! Solution (?): when adding a marked edge, delete all "earlier" marked edges
    for (F, _) in allWaysToAddOneMarked(FMarked; removeEarlierMarked=true)
        if allowMultiEdges(T)
            if T <: ProductFlag
                for (i, FT) in enumerate(fieldtypes(fieldtypes(T)[1]))
                    if allowMultiEdges(FT)
                        union!(F.marked, [e for e in FMarked.marked if e.i == i])
                    end
                end
            else
                F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
            end
        end
        if !withPropertyMarked(F)
            continue
        end

        cP = countEdges(F)[1:(end - 1)]

        if hasAtMostEdges(F.F, maxPredicates)
            push!(newFlags, F)
        end
    end
    return newFlags
end

"""
    generateAll(::Type{T}, maxVertices::Int, maxPredicates::Vector;
                initial_flag=one(T), use_unlabeled=true, parallel=true, withProperty=F -> true,
                withPropertyMarked=F -> true)

Generate flags of type `T` with up to `maxVertices` vertices and predicate counts
bounded by `maxPredicates`, extending `initial_flag`. The seed itself is always
included. `withProperty` filters each completed vertex layer;
`withPropertyMarked` prunes intermediate edge-marked states.

For partially labeled graphs and constant-weight codes (including induced
versions), generation first enumerates underlying objects, then inequivalent
ordered labelings compatible with the seed. `maxPredicates` is then
`[maxLabels, maxEdges]`. Existing seed labels stay fixed, and only vertices
outside the seed can acquire additional labels.

The coefficient samplers also use this path for induced models whose forbidden
flags do not depend on the labels: restrictions are checked on the underlying
objects before expanding their labelings.

Set `use_unlabeled=false` to use the original incremental generator. Custom
`withProperty` or `withPropertyMarked` callbacks and unsupported flag types
always use that generator, since pruning can depend on intermediate states.

Generation, canonicalization, and partial labeling use Julia's default thread
pool with batched scheduling and task-local buffers. Start Julia with
`--threads=N` to use `N` workers. Set `parallel=false` for serial execution;
callbacks must otherwise support concurrent calls.

Results are cached by argument values, including the bounds and seed. Treat
cached inputs and outputs as read-only; use `copy(generateAll(...))` before
modifying the returned vector.
"""
# The default IdDict compares array identities, so freshly constructed bounds
# and even the default one(T) seed would miss the cache on every call.
@memoize Dict function generateAll(
    ::Type{T},
    maxVertices::Int,
    maxPredicates::Vector;
    withProperty=_generation_accept_all,
    # withPropertyMarked=(F::EdgeMarkedFlag{T, predicateType(T)}) -> true,
    withPropertyMarked=_generation_accept_all,
    # withInducedProperty=(F::T) -> true,
    limit::Int=100_000,
    initial_flag=one(T),
    use_unlabeled::Bool=true,
    parallel::Bool=true,
) where {T}
    if use_unlabeled && _generation_unlabeled_callbacks(T, withProperty, withPropertyMarked) &&
        _can_generate_unlabeled(T, initial_flag, maxPredicates)
        return _generate_partially_labeled(
            T, maxVertices, maxPredicates, initial_flag, limit, parallel;
            withProperty, withPropertyMarked,
        )
    end
    generatedGraphs = Vector{T}[[initial_flag]]
    for i in (size(initial_flag) + 1):maxVertices
        layer = _generate_vertex_layer(
            generatedGraphs[end], i, maxPredicates, withProperty, withPropertyMarked, parallel
        )
        push!(generatedGraphs, layer)
    end
    return unique(vcat(generatedGraphs...))
end

# function generateAll_not_deterministic(
#     ::Type{T},
#     maxVertices::Int,
#     maxPredicates::Vector;
#     withProperty=(F::T) -> true,
#     # withPropertyMarked=(F::EdgeMarkedFlag{T, predicateType(T)}) -> true,
#     withPropertyMarked=(F) -> true,
#     # withInducedProperty=(F::T) -> true,
#     limit::Int=100_000,
#     initial_flag = one(T)
# ) where {T}
#     generatedGraphs = Vector{T}[Vector([initial_flag])]
#     @show maxPredicates
#     for i in size(initial_flag)+1:maxVertices
#         @show (i, maxVertices)
#         # nextGraphs = T[]
#         nextGraphs = Channel{T}(Inf)

#         pq = Channel{EdgeMarkedFlag{T,predicateType(T)}}(Inf)
#         # pq = PriorityQueue{EdgeMarkedFlag{T,predicateType(T)},Vector{Int}}()
#         # pq = PriorityQueue{EdgeMarkedFlag{T,predicateType(T)},Any}()

#         doneFlags = Set{EdgeMarkedFlag{T,predicateType(T)}}()
#         # doneFlags_lock = ReentrantLock()
#         doneFlags_lock = Base.Threads.SpinLock()

#         for f in generatedGraphs[i-size(initial_flag)]
#             newF = permute(f, 1:i)
#             # if newF == nothing 
#             #     continue 
#             # end

#             # @show newF
#             # @show size(newF)
#             # if withInducedProperty(newF) && 
#             if withProperty(newF)
#                 put!(nextGraphs, newF)
#             end
#             currentEdges = countEdges(newF)
#             # @show currentEdges
#             # @show length(currentEdges)
#             # @show currentEdges[length(maxPredicates):end]
#             # @show sum(currentEdges[length(maxPredicates):end])
#             # @show maxPredicates

#             if length(maxPredicates) < length(currentEdges) && (
#                 maxPredicates[end] isa Int &&
#                 maxPredicates[end] <= sum(sum.(currentEdges[length(maxPredicates):end]))
#             )
#                 continue
#             end

#             fixed = allowMultiEdges(T) ? Vector{Int}[] : [collect(1:(i - 1))]
#             uP::Vector{Vector{predicateType(T)}} = findUnknownPredicates(
#                 newF, fixed, maxPredicates
#             )
#             # @show uP
#             uP2 = findUnknownGenerationPredicates(newF, fixed, maxPredicates)
#             if uP2 !== nothing
#                 uP = vcat(uP, uP2)
#             end

#             if length(uP) == 1 && length(uP[1]) == 0
#                 continue
#             end

#             for i in 1:length(maxPredicates)
#                 if currentEdges[i] == maxPredicates[i]
#                     empty!(uP[i])
#                 end
#             end
#             # @show uP
#             uP = Vector{Vector{predicateType(T)}}(uP)
#             FMarked = EdgeMarkedFlag{T}(newF, uP)
#             for (F, _) in allWaysToAddOneMarked(FMarked; removeEarlierMarked=true)
#                 if allowMultiEdges(T)
#                     F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
#                 end
#                 # @show F
#                 # cP = countEdges(F)[1:(end - 1)]
#                 # @show cP, maxPredicates
#                 # @assert length(maxPredicates) == length(cP)
#                 # if length(maxPredicates) == length(cP) && all(cP .<= maxPredicates)
#                 #     # pq[F] = cP
#                 #     if !(F in doneFlags)
#                 #         @lock doneFlags_lock push!(doneFlags, F)
#                 #         put!(pq, F)
#                 #     end
#                 #     # @show "putting $F"
#                 # elseif all(
#                 #         cP[1:(length(maxPredicates) - 1)] .<= maxPredicates[1:(end - 1)]
#                 #     ) &&
#                 #     maxPredicates[end] isa Union{Int,Vector{Int}} &&
#                 #     sum(sum.(cP[length(maxPredicates):end])) <= sum(maxPredicates[end])
#                 #     # pq[F] = cP
#                 #     # if !(F in doneFlags)
#                 #     if !(F in doneFlags)
#                 #         @lock doneFlags_lock push!(doneFlags, F)
#                 #         put!(pq, F)
#                 #     end
#                 #     # put!(pq, F)
#                 #     # end
#                 #     # @show "putting $F"
#                 # end
#                 if hasAtMostEdges(F.F, maxPredicates)
#                     if !(F in doneFlags)
#                         @lock doneFlags_lock push!(doneFlags, F)
#                         put!(pq, F)
#                     end
#                 end
#             end
#         end

#         t = time()

#         tasks = []
#         # @show nextGraphs
#         # @show pq

#         # if length(pq) > 0 
#         if isready(pq)
#             noRunning = Threads.Atomic{Int}(0)
#             noRunningNow = 1
#             maxModels = 0
#             # @show noRunning[], Base.n_avail(pq), islocked(doneFlags_lock)
#             # t = @async process_edgeMarkedFlags(pq, nextGraphs, withProperty, maxPredicates, withPropertyMarked, T, doneFlags, doneFlags_lock, noRunning)
#             # push!(tasks, t)
#             # sleep(0.01)
#             for _ in 1:(Threads.nthreads() - 1)
#                 t = Threads.@spawn process_edgeMarkedFlags(
#                     pq,
#                     nextGraphs,
#                     withProperty,
#                     maxPredicates,
#                     withPropertyMarked,
#                     T,
#                     doneFlags,
#                     doneFlags_lock,
#                     noRunning,
#                 )
#                 errormonitor(t)
#                 push!(tasks, t)
#             end
#             # @show tasks
#             while isready(pq) || noRunningNow > 0
#                 noRunningNow = noRunning[]
#                 noModels = Base.n_avail(pq)
#                 if noModels > maxModels
#                     maxModels = noModels
#                 end
#                 if maxModels > limit
#                     close(pq)
#                     return :limit
#                 end
#                 print(
#                     "\r$(noRunningNow) active threads, \t$(noModels) models left,\t $maxModels max models\t\t\t",
#                 )
#                 sleep(0.1)
#             end
#             println()
#             # @show noRunning[]
#             close(pq)
#             # @info "closed"
#             # @show noRunning[]

#             wait.(tasks)
#         end

#         close(nextGraphs)
#         nextGraphs = collect(nextGraphs)

#         # while !isempty(pq)

#         #     # end
#         # end

#         # @show length(nextGraphs)
#         unique!(nextGraphs)
#         @show length(nextGraphs)
#         k = length(nextGraphs)
#         res = T[]
#         t = time()
#         for (i, G) in enumerate(nextGraphs)
#             if time() - t > 1
#                 @show i, k
#                 t = time()
#             end
#             push!(res, labelCanonically(G))
#         end
#         unique!(res)

#         push!(generatedGraphs, res)
#         # push!(generatedGraphs, unique(labelCanonically.(nextGraphs)))
#     end
#     return unique(vcat(generatedGraphs...))
# end
