export generateAll

include("SchreierSims.jl")

using DataStructures

# Custom implementation of nauty, but still sloooow
# Allows us to label near-arbitrary combinatoric objects
function label(F::T; prune=true, removeIsolated=true) where {T}
    # @show F 
    # display(F)
    # @show isolatedVertices(F)
    if removeIsolated
        isoV = isolatedVertices(F)
        if any(isoV)
            F = subFlag(F, .!isoV)
        end
    end

    n = size(F)

    if n == 0
        return F, Group(), []
    end

    nInv1 = UInt[]
    nInvStar = UInt[]
    p1 = Int[]
    pStar = Int[]

    autG = Group()

    first = true

    v1 = zeros(Int, n)
    vStar = zeros(Int, n)

    curBranch = Int[]
    covered = Vector{Int}[]

    # To avoid allocations in refine!
    alpha = BitVector(undef, n)
    # newCellSizes = zeros(Int, n)

    vertDistinguish = zeros(UInt, n)

    # Q = UInt[0 for i in 1:n, j in 1:n]
    Q = zeros(UInt, n, n)
    WCellInd = BitVector(undef, n)
    curCell = BitVector(undef, n)
    newCells = Dict{UInt,Int}()

    function refine!(coloring::Vector{Int})
        Q .= 0
        @inbounds while any(alpha) && maximum(coloring) < n
            W = findfirst(alpha)
            WCellInd .= coloring .== W
            alpha[W] = false

            cell = 1
            while cell <= maximum(coloring)
                vertDistinguish .= 0
                curCell .= coloring .== cell

                empty!(newCells)
                # newCells = Dict{UInt,Int}()

                for v in findall(curCell)#findall(x->x==cell, coloring)
                    d = distinguish(F, v, WCellInd)
                    vertDistinguish[v] = d
                    # union!(newCells, [d])
                    newCells[d] = get(newCells, d, 0) + 1
                end

                # To make it invariant of initial vertex labeling, sort the hashes
                # newCells = Dict(d=>i+cell-1 for (i,d) in enumerate(sort!([u for u in unique(vertDistinguish) if u != 0])))

                # newCellSizes = Dict(d=>count(x->x==d, vertDistinguish) for d in keys(newCells))

                numNewCells = length(newCells) - 1

                for i in eachindex(coloring)
                    if coloring[i] > cell
                        coloring[i] += numNewCells
                    end
                end

                # coloring[coloring .> cell] .+= numNewCells
                for i in length(alpha):-1:(cell+numNewCells+1)
                    alpha[i] = alpha[i-numNewCells]
                end
                # @views alpha[(cell + numNewCells + 1):end] .= alpha[(cell + 1):(end - numNewCells)]

                alpha[(cell+1):(cell+numNewCells)] .= true

                newCellsCol = collect(newCells)
                sort!(newCellsCol; by=x -> x[1])

                # sorting newCellsCol by hashes breaks things?!? But I need to sort!

                for v in findall(curCell)#findall(x->x==cell, coloring)
                    # coloring[v] = newCells[vertDistinguish[v]]

                    d = vertDistinguish[v]
                    coloring[v] = findfirst(x -> x[1] == d, newCellsCol) + cell - 1
                    Q[coloring[v], W > cell ? W + numNewCells : W] = d

                    # Q = hash(Q, vertDistinguish[v])
                end

                if !alpha[cell]
                    alpha[cell] = true

                    maxCellSize = 0
                    maxCellInd = 0
                    for (i, (d, s)) in enumerate(newCellsCol)
                        if s > maxCellSize
                            maxCellSize = s
                            maxCellInd = i
                        end
                    end

                    # Remove biggest new cell
                    alpha[maxCellInd+cell-1] = false
                end

                cell += length(newCellsCol)
            end
        end

        cl = maximum(coloring)
        nodeInvariant = hash(Q, hash([count(x -> x == i, coloring) for i in 1:cl]))

        if maximum(coloring) == n
            # append permuted Flag
            # return UInt[nodeInvariant, hash(permute(F, coloring))]
            # return nodeInvariant, hash(permute(F, coloring))

            return [nodeInvariant, hash(permute(F, coloring))]
            # return hash(nodeInvariant, hash(permute(F, coloring)))
        end
        return nodeInvariant
    end

    function individualize!(coloring::Vector{Int}, v::Int)
        for i in 1:n
            if coloring[i] >= coloring[v] && i != v
                coloring[i] += 1
            end
        end
        return coloring
    end

    function refine!(coloring::Vector{Int}, v::Int)
        alpha .= false
        alpha[coloring[v]] = true
        individualize!(coloring, v)
        nodeInv = refine!(coloring)
        return nodeInv
    end

    function investigateNode(coloring::Vector{Int}, nodeInv=UInt[])
        if maximum(coloring) == n

            # check for automorphisms
            if !first
                p2 = coloring
                autom1 = v1[p2]
                changed = false
                if F == permute(F, autom1)
                    changed = addGen!(autG, autom1)
                end
                autom2 = vStar[p2]
                if F == permute(F, autom2)
                    changed |= addGen!(autG, autom2)
                end

                # if changed, check for automorphism pruning higher up the tree
                if changed
                    # @info "Added onto stabilizer, new order is $(order(autG))"
                    stabilizer!(autG, curBranch)
                    for i in 1:length(curBranch)
                        H = stabilizer!(autG, curBranch[1:(i-1)])

                        o = covered[i]
                        orbit!(H, o)
                        if prune && curBranch[i] in o
                            # cut this branch multiple levels up
                            difLevel = length(curBranch) - i
                            curBranch = curBranch[1:i]
                            covered = covered[1:i]
                            # @info "Pruning $difLevel levels from level $(length(curBranch)) via automorphism."
                            return difLevel
                        end
                    end
                end
            end

            # improve v1 and vStar
            if first #|| nodeInv < nInv1
                for i in 1:n
                    v1[coloring[i]] = i
                end
                nInv1 = nodeInv
            end
            if first || nodeInv > nInvStar
                for i in 1:n
                    vStar[coloring[i]] = i
                end
                nInvStar = nodeInv
            end
            first = false
        else
            # pruning 
            @assert first ||
                    length(nodeInv) <= length(nInvStar) ||
                    length(nodeInv) <= length(nInv1)

            if prune &&
               (!first) &&
               (
                   !(
                       nodeInv[1:min(length(nodeInv), length(nInv1))] ==
                       nInv1[1:min(length(nodeInv), length(nInv1))]
                   )
               ) &&
               (
                   !(
                       nodeInv[1:min(length(nodeInv), length(nInvStar))] >=
                       nInvStar[1:min(length(nodeInv), length(nInvStar))]
                   )
               )
                return 0
            end
            firstBigCell = Int[]
            for i in 1:n
                c = findall(x -> x == i, coloring)
                if length(c) > 1
                    firstBigCell = c
                    break
                end
            end

            push!(covered, Int[])
            for i in firstBigCell
                if i in covered[end] && prune
                    # @info "Prune $(vcat(curBranch,[i])) via automorphism"
                    continue
                end
                newC = copy(coloring)
                newNodeInv = refine!(newC, i)
                push!(curBranch, i)
                t = investigateNode(newC, vcat(nodeInv, newNodeInv))
                if t > 0
                    return t - 1
                end
                pop!(curBranch)

                union!(covered[end], [i])
                orbit!(stabilizer!(autG, curBranch), covered[end])
            end
            pop!(covered)
        end

        return 0
    end

    col = Int[vertexColor(F, v) for v in 1:n]
    alpha[1] = true
    refine!(col)

    investigateNode(col)
    p = [findfirst(x -> x == i, vStar) for i in 1:n]

    return permute(F, p), permute!(autG, p), p
end

function generateAll(::Type{F}, maxVertices::Int, maxEdges::Int; withProperty=(F::F) -> true) where {F}
    return generateAll(F, maxVertices, [maxEdges]; withProperty=withProperty)
end

#TODO: Quite a bit slower than nauty/traces, how are they doing it?
"""
    generateAll(::Type{F}, maxVertices::Int, maxPredicates::Vector{Int}; withProperty = (F::T) -> true) where {F}

Generates all Flags of type `F` with up to `maxVertices` vertices and up to `maxPredicates` non-zero predicate values. 'maxPredicates' is a vector, for the case that there are multiple predicates. If a function `withProperty:F->{true, false}` is given, keeps adding edges to flags as long as the property holds.
"""
function generateAll(::Type{T}, maxVertices::Int, maxPredicates::Vector; withProperty=(F::T) -> true) where {T}
    generatedGraphs = Vector{T}[Vector([one(T)])]
    for i in 1:maxVertices
        nextGraphs = T[]

        pq = PriorityQueue{EdgeMarkedFlag{T,predicateType(T)},Vector}()

        for f in generatedGraphs[i]
            newF = permute(f, 1:i)

            # @show newF
            # @show size(newF)
            push!(nextGraphs, newF)
            currentEdges = countEdges(newF)
            # @show currentEdges
            # @show length(currentEdges)
            # @show currentEdges[length(maxPredicates):end]
            # @show sum(currentEdges[length(maxPredicates):end])
            # @show maxPredicates

            if length(maxPredicates) < length(currentEdges) && (maxPredicates[end] isa Int && maxPredicates[end] <= sum(sum.(currentEdges[length(maxPredicates):end])))
                continue
            end


            fixed = allowMultiEdges(T) ? Vector{Int}[] : [collect(1:(i-1))]
            uP = findUnknownPredicates(newF, fixed, maxPredicates)
            # @show uP
            uP2 = findUnknownGenerationPredicates(newF, fixed, maxPredicates)
            if uP2 !== nothing
                uP = vcat(uP, uP2)
            end

            if length(uP) == 1 && length(uP[1]) == 0
                continue
            end

            for i = 1:length(maxPredicates)
                if currentEdges[i] == maxPredicates[i]
                    empty!(uP[i])
                end
            end
            # @show uP
            uP = Vector{Vector{Any}}(uP)
            FMarked = EdgeMarkedFlag{T}(newF, uP)
            for (F, _) in allWaysToAddOneMarked(FMarked)
                if allowMultiEdges(T)
                    F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
                end
                cP = countEdges(F)[1:(end-1)]
                # @assert length(maxPredicates) == length(cP)
                if length(maxPredicates) == length(cP) && all(cP .<= maxPredicates)
                    pq[F] = cP
                elseif all(cP[1:length(maxPredicates)-1] .<= maxPredicates[1:end-1]) && maxPredicates[end] isa Int && sum(sum.(cP[length(maxPredicates):end])) <= maxPredicates[end]
                    pq[F] = cP
                end
            end
        end

        while !isempty(pq)
            FMarked = dequeue!(pq)
            # @show (length(pq), sum(countEdges(FMarked.F)))
            # @show FMarked
            if withProperty(FMarked.F)
                # continue
                push!(nextGraphs, FMarked.F)
            end
            cP = countEdges(FMarked.F)
            if length(maxPredicates) == length(cP) && all(cP .== maxPredicates)
                continue
            elseif all(cP[1:length(maxPredicates)-1] .== maxPredicates[1:end-1]) && sum(cP[length(maxPredicates):end]) == maxPredicates[end]
                continue
            end
            # if !all(countEdges(FMarked.F) .== maxPredicates)
            for (F, _) in allWaysToAddOneMarked(FMarked)
                if allowMultiEdges(T)
                    F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
                end
                # @assert sum(countEdges(FMarked.F)) < sum(countEdges(F.F))
                if !withProperty(F.F)
                    continue
                end
                cP = countEdges(F)[1:(end-1)]
                # if all(cP .<= maxPredicates)
                #     pq[F] = cP
                # end
                if length(maxPredicates) == length(cP) && all(cP .<= maxPredicates)
                    pq[F] = cP
                elseif all(cP[1:length(maxPredicates)-1] .<= maxPredicates[1:end-1]) && sum(sum.(cP[length(maxPredicates):end])) <= maxPredicates[end]
                    pq[F] = cP
                end
            end
            # end
        end

        push!(generatedGraphs, unique(labelCanonically.(nextGraphs)))
    end
    return unique(vcat(generatedGraphs...))
end
