# Pre-parallel rewrite incremental generator, evaluated in FlagSOS for exact
# comparisons. Its original queue is consumed serially to keep the reference
# independent of the new scheduler and safe at large test thread counts.
function _generation_reference(
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
) where {T}
    generatedGraphs = Vector{T}[Vector([initial_flag])]
    # @show maxPredicates
    for i in (size(initial_flag) + 1):maxVertices
        # @show (i, maxVertices)
        nextGraphs = Set{T}()
        nextGraphs_lock = Base.Threads.SpinLock()

        flags = Channel{EdgeMarkedFlag{T,predicateType(T)}}(Inf)
        flags_to_process = Threads.Atomic{Int}(0)

        doneFlags = Set{UInt64}()
        doneFlags_lock = Base.Threads.SpinLock()

        for f in generatedGraphs[i - size(initial_flag)]
            newF = permute(f, 1:i)
            if withProperty(newF)
                push!(nextGraphs, newF)
            end
            currentEdges = countEdges(newF)

            if length(maxPredicates) < length(currentEdges) && (
                maxPredicates[end] isa Int &&
                maxPredicates[end] <= sum(sum.(currentEdges[length(maxPredicates):end]))
            )
                continue
            end

            fixed = allowMultiEdges(T) ? Vector{Int}[] : [collect(1:(i - 1))]
            uP::Vector{Vector{predicateType(T)}} = findUnknownPredicates(
                newF, fixed, maxPredicates
            )
            uP2 = findUnknownGenerationPredicates(newF, fixed, maxPredicates)
            if uP2 !== nothing
                uP = vcat(uP, uP2)
            end

            if length(uP) == 1 && length(uP[1]) == 0
                continue
            end

            for i in 1:length(maxPredicates)
                if currentEdges[i] == maxPredicates[i]
                    empty!(uP[i])
                end
            end
            # @show uP
            uP = Vector{Vector{predicateType(T)}}(uP)
            FMarked = EdgeMarkedFlag{T}(newF, uP)
            for (F, _) in allWaysToAddOneMarked(FMarked; removeEarlierMarked=true)
                if allowMultiEdges(T)
                    F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
                end
                if hasAtMostEdges(F.F, maxPredicates)
                    hF = hash(F)
                    @lock doneFlags_lock if !(hF in doneFlags)
                        push!(doneFlags, hF)
                        atomic_add!(flags_to_process, 1)
                        put!(flags, F)
                    end
                end
            end
        end

        t = time()

        last_print_time = Threads.Atomic{Float64}(time())
        maxModels = Threads.Atomic{Int}(flags_to_process[])
        print_lock = ReentrantLock()
        # @show isready(flags)

        if isready(flags)
            for _ in 1:1
                # @show isready(flags)
                for FMarked in flags
                    # @show FMarked
                    now = time()
                    # Check if 1.0 second has passed
                    if now - last_print_time[] > 1.0
                        lock(print_lock) do
                            # Double-check inside lock to prevent race condition
                            if now - last_print_time[] > 1.0
                                print(
                                    "\rGen flags ($i / $maxVertices) ... $(flags_to_process[]) models left,\t $(maxModels[]) max models        \t\t\t",
                                )
                                last_print_time[] = now
                            end
                        end
                    end

                    if withProperty(FMarked.F)
                        @lock nextGraphs_lock push!(nextGraphs, FMarked.F)
                    end
                    # also edge marked!
                    newFlags = process_edgeMarkedFlags(FMarked, maxPredicates, withPropertyMarked, T)

                    for F in newFlags
                        addF = false
                        hF = hash(F)
                        @lock doneFlags_lock if !(hF in doneFlags)
                            push!(doneFlags, hF)
                            addF = true
                        end
                        if addF
                            atomic_add!(flags_to_process, 1)
                            atomic_max!(maxModels, flags_to_process[])
                            put!(flags, F)
                        end
                    end

                    atomic_sub!(flags_to_process, 1)

                    if flags_to_process[] == 0
                        close(flags)
                    end
                end
            end
        else 
            close(flags)
        end

        # nextGraphs = collect(nextGraphs)

        # @show length(nextGraphs)
        k = length(nextGraphs)
        res = T[]
        t = time()
        for (i, G) in enumerate(nextGraphs)
            if time() - t > 1
                @show i, k
                t = time()
            end
            push!(res, labelCanonically(G))
        end
        unique!(res)

        push!(generatedGraphs, res)
    end
    return unique(vcat(generatedGraphs...))
end
