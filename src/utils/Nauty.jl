
include("SchreierSims.jl")

using DataStructures

# Custom implementation of nauty, but still sloooow
# Allows us to label near-arbitrary combinatoric objects
function label(F::T; prune = true, removeIsolated = true) where{T}
    if removeIsolated
        isoV = isolatedVertices(F)
        if any(isoV)
            F = subFlag(F, .! isoV)
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

    numNode = 1

    # To avoid allocations in refine!
    alpha = BitVector(undef, n)
    # newCellSizes = zeros(Int, n)

    vertDistinguish = zeros(UInt, n)

    Q = UInt[0 for i = 1:n, j = 1:n]
    WCellInd = BitVector(undef, n)
    curCell = BitVector(undef, n)


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

                newCells = Dict{UInt, Int}()

                for v in findall(curCell)#findall(x->x==cell, coloring)
                    @views d = hash(distinguish(F, v, WCellInd))
                    vertDistinguish[v] = d
                    # union!(newCells, [d])
                    newCells[d] = get(newCells, d, 0) + 1
                end

                # To make it invariant of initial vertex labeling, sort the hashes
                # newCells = Dict(d=>i+cell-1 for (i,d) in enumerate(sort!([u for u in unique(vertDistinguish) if u != 0])))
                


                # newCellSizes = Dict(d=>count(x->x==d, vertDistinguish) for d in keys(newCells))

                numNewCells = length(newCells) - 1

                coloring[coloring .> cell] .+= numNewCells
                alpha[cell+numNewCells + 1:end] .= alpha[cell+1:end-numNewCells]


                alpha[cell+1:cell+numNewCells] .= true


                newCellsCol = collect(newCells)
                sort!(newCellsCol, by = x->x[1])

                # sorting newCellsCol by hashes breaks things?!? But I need to sort!

                for v in findall(curCell)#findall(x->x==cell, coloring)
                    # coloring[v] = newCells[vertDistinguish[v]]

                    d = vertDistinguish[v]
                    coloring[v] = findfirst(x->x[1] == d, newCellsCol) + cell - 1
                    Q[coloring[v], W > cell ? W + numNewCells : W] = d

                    # Q = hash(Q, vertDistinguish[v])
                end

                if !alpha[cell]
                    alpha[cell] = true
                    
                    maxCellSize =  0
                    maxCellInd = 0
                    for (i,(d, s)) in enumerate(newCellsCol)
                        if s > maxCellSize
                            maxCellSize = s
                            maxCellInd = i
                        end
                    end

                    # Remove biggest new cell
                    alpha[maxCellInd + cell - 1] = false
                end
                
                cell += length(newCellsCol)
            end
        end


        cl = maximum(coloring)
        nodeInvariant = hash(Q, hash([count(x->x==i, coloring) for i = 1:cl]))

        if maximum(coloring) == n
            # append permuted Flag
            return [nodeInvariant, hash(permute(F, coloring))]
        end
        return nodeInvariant
    end

    function individualize!(coloring::Vector{Int}, v::Int)
        for i = 1:n 
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

    function investigateNode(coloring::Vector{Int}, nodeInv = UInt[])
        numNode += 1

        if maximum(coloring) == n

            # check for automorphisms
            if !first
                p2 = coloring
                autom1 = v1[p2]
                changed = false
                if F == permute(F,autom1)
                    changed = addGen!(autG, autom1)
                end
                autom2 = vStar[p2]
                if F == permute(F,autom2)
                    changed |= addGen!(autG, autom2)
                end

                # if changed, check for automorphism pruning higher up the tree
                if changed
                    # @info "Added onto stabilizer, new order is $(order(autG))"
                    stabilizer!(autG, curBranch)
                    for i in 1:length(curBranch)
                        H = stabilizer!(autG, curBranch[1:i-1])
                        
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
                for i = 1:n
                    v1[coloring[i]] = i
                end
                nInv1 = nodeInv
            end
            if first || nodeInv > nInvStar
                for i = 1:n
                    vStar[coloring[i]] = i
                end
                nInvStar = nodeInv
            end
            first = false
        else
            # pruning 
            @assert first || length(nodeInv) <= length(nInvStar) || length(nodeInv) <= length(nInv1)

            if prune && (!first) && (! (nodeInv[1:min(length(nodeInv), length(nInv1))] == nInv1[1:min(length(nodeInv), length(nInv1))])) && (! (nodeInv[1:min(length(nodeInv), length(nInvStar))] >= nInvStar[1:min(length(nodeInv), length(nInvStar))]))
                return 0
            end
            firstBigCell = Int[]
            for i = 1:n
                c = findall(x->x==i, coloring)
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
                    return t-1
                end
                pop!(curBranch)
                
                union!(covered[end], [i])
                orbit!(stabilizer!(autG, curBranch), covered[end])
            end
            pop!(covered)
        end

        return 0
    end

    col = [vertexColor(F, v) for v = 1:n]
    alpha[1] = true
    refine!(col)

    investigateNode(col)
    p = [findfirst(x->x==i,vStar) for i = 1:n]

    return permute(F, p), permute!(autG, p), p
end



function generateAll(::Type{F}, maxVertices::Int, maxEdges::Int) where {F}
    return generateAll(F, maxVertices, [maxEdges])
end


#TODO: Quite a bit slower than nauty/traces, how are they doing it?
"""
    generateAll(::Type{F}, maxVertices::Int, maxPredicates::Vector{Int}) where {F}

Generates all Flags of type `F` with up to `maxVertices` vertices and up to `maxPredicates` non-zero predicate values. 'maxPredicates' is a vector, for the case that there are multiple predicates.
"""
function generateAll(::Type{T}, maxVertices::Int, maxPredicates::Vector{Int}) where {T}
    generatedGraphs = Vector{T}[Vector([one(T)])]
    for i = 1:maxVertices
        nextGraphs = T[]

        pq = PriorityQueue{EdgeMarkedFlag{T}, Vector{Int}}()

        for f in generatedGraphs[i]
            newF = permute(f, 1:i)
            uP = findUnknownPredicates(newF, [collect(1:i-1)])
            push!(nextGraphs, newF)
            if length(uP) == 1 && length(uP[1]) == 0
                continue
            end

            FMarked = EdgeMarkedFlag{T}(newF, uP)
            for (F,_) in allWaysToAddOneMarked(FMarked)
                cP = countEdges(F)[1:end-1]
                if all(cP .<= maxPredicates)
                    pq[F] = cP
                end
            end
        end

        while !isempty(pq)
            FMarked = dequeue!(pq)
            push!(nextGraphs, FMarked.F)
            for (F,_) in allWaysToAddOneMarked(FMarked)
                cP = countEdges(F)[1:end-1]
                if all(cP .<= maxPredicates)
                    pq[F] = cP
                end
            end
        end

        push!(generatedGraphs, unique(labelCanonically.(nextGraphs)))
    end
    return unique(vcat(generatedGraphs...))
end