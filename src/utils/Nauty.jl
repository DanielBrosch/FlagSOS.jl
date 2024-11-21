export generateAll

include("SchreierSims.jl")

using DataStructures

# function refine!(F::T, coloring::Vector{Int}, alpha)::Vector{UInt} where {T<:Flag}
#     # Q .= 0

# end

# function individualize!(coloring::Vector{Int}, v::Int)::Vector{Int}
#     return coloring
# end

function refine!(coloring::Vector{Int}, F, v::Int)::Vector{UInt}
    n = size(F)
    alpha = BitVector(undef, n)
    vertDistinguish = zeros(UInt, n)
    alpha .= false
    if v == 0
        alpha[1] = true
    else
        alpha[coloring[v]] = true
        # individualize!(coloring, v)
        for i in 1:n
            if coloring[i] >= coloring[v] && i != v
                coloring[i] += 1
            end
        end
    end

    # nodeInv = refine!(coloring)
    Q = zeros(UInt, n, n)
    curCell::BitVector = BitVector(undef, n)
    @inbounds while maximum(coloring) < n
        W::Int = 0
        for i in 1:length(alpha)
            if alpha[i]
                W = i
                break
            end
        end
        if W == 0
            break
        end
        # W::Int = findfirst(alpha)
        # WCellInd .= coloring .== W
        WCellInd::BitVector = coloring .== W
        alpha[W] = false

        cell::Int = 1
        newCells = Dict{UInt,Int}()
        while cell <= maximum(coloring)
            vertDistinguish .= 0
            # curCell .= coloring .== cell
            for i in 1:n
                curCell[i] = coloring[i] == cell
            end

            empty!(newCells)

            for v in findall(curCell)#findall(x->x==cell, coloring)
                d::UInt = distinguish(F, v, WCellInd)
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
            for i in length(alpha):-1:(cell + numNewCells + 1)
                alpha[i] = alpha[i - numNewCells]
            end
            # @views alpha[(cell + numNewCells + 1):end] .= alpha[(cell + 1):(end - numNewCells)]

            alpha[(cell + 1):(cell + numNewCells)] .= true

            newCellsCol::Vector{Pair{UInt,Int}} = collect(newCells)
            sort!(newCellsCol; by=x -> x[1])

            # sorting newCellsCol by hashes breaks things?!? But I need to sort!

            for v in 1:n
                !curCell[v] && continue
                # findall(curCell)#findall(x->x==cell, coloring)
                # coloring[v] = newCells[vertDistinguish[v]]

                d::UInt = vertDistinguish[v]
                firstPos::Int = 0
                for i in 1:length(newCellsCol)
                    if newCellsCol[i][1] == d
                        firstPos = i
                        break
                    end
                end
                @assert firstPos > 0

                # findfirst(x -> x[1] == d, newCellsCol)
                coloring[v] = firstPos + cell - 1
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
                alpha[maxCellInd + cell - 1] = false
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
        return UInt[nodeInvariant, hash(permute(F, coloring))]
        # return hash(nodeInvariant, hash(permute(F, coloring)))
    end
    return UInt[nodeInvariant]
    # return nodeInv
end

function investigateNode(
    F,
    coloring::Vector{Int},
    nodeInv::Vector{UInt},
    n,
    nInv1,
    nInvStar,
    autG,
    v1,
    vStar,
    curBranch,
    covered,
    prune,
)::Int
    # @info "investigate node at $coloring, $nodeInv"

    first = length(nInv1) == 0

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
                    H = stabilizer!(autG, curBranch[1:(i - 1)])

                    @assert H !== nothing

                    o = covered[i]
                    orbit!(H, o)
                    if prune && curBranch[i] in o
                        # cut this branch multiple levels up
                        difLevel = length(curBranch) - i
                        resize!(curBranch, i)
                        resize!(covered, i)
                        # covered = covered[1:i]
                        # @info "Pruning $difLevel levels from level $(length(curBranch)) via automorphism."
                        return difLevel
                    end
                end
            end
        end

        # improve v1 and vStar
        # if first #|| nodeInv < nInv1
        if first || nodeInv < nInv1
            for i in 1:n
                v1[coloring[i]] = i
            end
            resize!(nInv1, length(nodeInv))
            nInv1 .= nodeInv
            # nInv1 = nodeInv
        end
        if first || nodeInv > nInvStar
            for i in 1:n
                vStar[coloring[i]] = i
            end
            resize!(nInvStar, length(nodeInv))
            nInvStar .= nodeInv
            # nInvStar = nodeInv
        end
        first = false
    else
        # pruning
        # if !(first ||
        #      length(nodeInv) <= length(nInvStar) ||
        #      length(nodeInv) <= length(nInv1))
        #     @show F
        #     display(F)
        #     @show typeof(F)
        #     global errorFlag = deepcopy(F)
        #     @show first
        #     @show nodeInv
        #     @show nInvStar
        #     @show nInv1
        # end

        # assertion wrong! nodeInv may be longer than nInvStar! We want the lexicographically largest hash vector, not smallest.
        # @assert first ||
        #         length(nodeInv) <= length(nInvStar) ||
        #         length(nodeInv) <= length(nInv1)
        # @assert first ||
        #         nodeInv[1:min(length(nodeInv), length(nInvStar))] >= nInvStar[1:min(length(nodeInv), length(nInvStar))] ||
        #         length(nodeInv) <= length(nInv1)

        @views if prune &&
            !first &&
            !(
                nodeInv[1:min(length(nodeInv), length(nInv1))] ==
                nInv1[1:min(length(nodeInv), length(nInv1))]
            ) &&
            !(
                nodeInv[1:min(length(nodeInv), length(nInvStar))] >=
                nInvStar[1:min(length(nodeInv), length(nInvStar))]
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
            if prune && i in covered[end]
                # @info "Prune $(vcat(curBranch,[i])) via automorphism"
                continue
            end
            newC::Vector{Int} = copy(coloring)
            newNodeInv::Vector{UInt} = refine!(newC, F, i)
            push!(curBranch, i)
            catNodeInv::Vector{UInt} = vcat(nodeInv, newNodeInv)
            t = investigateNode(
                F,
                newC,
                catNodeInv,
                n,
                nInv1,
                nInvStar,
                autG,
                v1,
                vStar,
                curBranch,
                covered,
                prune,
            )

            if t > 0
                return t - 1
            end
            pop!(curBranch)

            # union!(covered[end], [i])
            if prune || !(i in covered[end])
                push!(covered[end], i)
            end
            H = stabilizer!(autG, curBranch)
            @assert H !== nothing
            orbit!(H, covered[end])
        end
        pop!(covered)
    end

    return 0
end

# Custom implementation of nauty, but still sloooow
# Allows us to label near-arbitrary combinatoric objects
function label(F::T; prune=true, removeIsolated=true) where {T}
    # @show F 
    # display(F)
    # @show isolatedVertices(F)

    if size(F) > 0 && removeIsolated
        isoV = isolatedVertices(F)
        # @show typeof(isoV)
        if any(isoV)
            # @show F 
            # @show isolatedVertices(F)
            # @show isoV
            # @show typeof(isoV)
            # @show typeof(map(!,isoV))

            # F = T(subFlag(F, map(!,isoV)))
            return label(
                subFlag(F, map(!, isoV)); prune=prune, removeIsolated=removeIsolated
            )
        end
    end

    n::Int = size(F)

    if n == 0
        return F, Group(), []
    end

    nInv1::Vector{UInt} = UInt[]
    nInvStar::Vector{UInt} = UInt[]
    # p1 = Int[]
    # pStar = Int[]

    autG::Group = Group()

    # first = true

    v1::Vector{Int} = zeros(Int, n)
    vStar::Vector{Int} = zeros(Int, n)

    curBranch::Vector{Int} = Int[]
    covered::Vector{Vector{Int}} = Vector{Int}[]

    # To avoid allocations in refine!
    # alpha = BitVector(undef, n)
    # vertDistinguish = zeros(UInt, n)

    # Q = zeros(UInt, n, n)
    # WCellInd = BitVector(undef, n)
    # curCell = BitVector(undef, n)
    # newCells = Dict{UInt,Int}()

    col::Vector{Int} = Int[vertexColor(F, v) for v in 1:n]
    # alpha[1] = true
    refine!(col, F, 0)

    investigateNode(
        F, col, UInt[], n, nInv1, nInvStar, autG, v1, vStar, curBranch, covered, prune
    )

    p = zeros(Int, n)
    p[vStar] .= 1:n
    # p = Int[findfirst(x -> x == i, vStar) for i in 1:n]
    # @assert p == p2
    return permute(F, p), permute!(autG, p), p
end

function generateAll(
    ::Type{F}, maxVertices::Int, maxEdges::Int; withProperty=(F::F) -> true
) where {F}
    return generateAll(F, maxVertices, [maxEdges]; withProperty=withProperty)
end

#TODO: Quite a bit slower than nauty/traces, how are they doing it?
"""
    generateAll(::Type{F}, maxVertices::Int, maxPredicates::Vector{Int}; withProperty = (F::T) -> true) where {F}

Generates all Flags of type `F` with up to `maxVertices` vertices and up to `maxPredicates` non-zero predicate values. 'maxPredicates' is a vector, for the case that there are multiple predicates. If a function `withProperty:F->{true, false}` is given, keeps adding edges to flags as long as the property holds.
"""
function generateAll(
    ::Type{T},
    maxVertices::Int,
    maxPredicates::Vector;
    withProperty=(F::T) -> true,
    withInducedProperty=(F::T) -> true,
) where {T}
    generatedGraphs = Vector{T}[Vector([one(T)])]
    for i in 1:maxVertices
        @show (i, maxVertices)
        nextGraphs = T[]

        # pq = PriorityQueue{EdgeMarkedFlag{T,predicateType(T)},Vector{Int}}()
        pq = PriorityQueue{EdgeMarkedFlag{T,predicateType(T)},Any}()

        for f in generatedGraphs[i]
            newF = permute(f, 1:i)
            # if newF == nothing 
            #     continue 
            # end

            # @show newF
            # @show size(newF)
            if withInducedProperty(newF)
                push!(nextGraphs, newF)
            end
            currentEdges = countEdges(newF)
            # @show currentEdges
            # @show length(currentEdges)
            # @show currentEdges[length(maxPredicates):end]
            # @show sum(currentEdges[length(maxPredicates):end])
            # @show maxPredicates

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
            # @show uP
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
            for (F, _) in allWaysToAddOneMarked(FMarked)
                if allowMultiEdges(T)
                    F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
                end
                # @show F
                cP = countEdges(F)[1:(end - 1)]
                # @show cP
                # @assert length(maxPredicates) == length(cP)
                if length(maxPredicates) == length(cP) && all(cP .<= maxPredicates)
                    pq[F] = cP
                elseif all(
                        cP[1:(length(maxPredicates) - 1)] .<= maxPredicates[1:(end - 1)]
                    ) &&
                    maxPredicates[end] isa Union{Int,Vector{Int}} &&
                    sum(sum.(cP[length(maxPredicates):end])) <= sum(maxPredicates[end])
                    pq[F] = cP
                end
            end
        end

        t = time()

        while !isempty(pq)

            if time() - t > 1 
                @show length(pq)
                t = time()
            end
            FMarked = dequeue!(pq)
            # @show (length(pq), sum(countEdges(FMarked.F)))
            # @show FMarked
            if withInducedProperty(FMarked.F)
                # continue
                push!(nextGraphs, FMarked.F)
            end
            cP = countEdges(FMarked.F)
            if length(maxPredicates) == length(cP) && all(cP .== maxPredicates)
                continue
            elseif all(cP[1:(length(maxPredicates) - 1)] .== maxPredicates[1:(end - 1)]) &&
                sum(cP[length(maxPredicates):end]) == maxPredicates[end]
                continue
            end
            # if !all(countEdges(FMarked.F) .== maxPredicates)
            for (F, _) in allWaysToAddOneMarked(FMarked)
                if allowMultiEdges(T)
                    # @show FMarked.marked
                    # @show F.marked
                    if T <: ProductFlag
                        for (i, FT) in enumerate(fieldtypes(fieldtypes(T)[1]))
                            if allowMultiEdges(FT)
                                union!(F.marked, [e for e in FMarked.marked if e[1] == i])
                            end
                        end
                    else
                        F = EdgeMarkedFlag{T}(F.F, FMarked.marked)
                    end
                end
                # @assert sum(countEdges(FMarked.F)) < sum(countEdges(F.F))
                if !withProperty(F.F)
                    continue
                end

                cP = countEdges(F)[1:(end - 1)]
                # if all(cP .<= maxPredicates)
                #     pq[F] = cP
                # end
                # @show maxPredicates
                # @show cP
                if length(maxPredicates) == length(cP) && all(cP .<= maxPredicates)
                    pq[F] = cP
                elseif maxPredicates[end] isa Int &&
                    all(cP[1:(length(maxPredicates) - 1)] .<= maxPredicates[1:(end - 1)]) &&
                    sum(sum.(cP[length(maxPredicates):end])) <= maxPredicates[end]
                    pq[F] = cP
                end
            end
            # end
        end

        push!(generatedGraphs, unique(labelCanonically.(nextGraphs)))
    end
    return unique(vcat(generatedGraphs...))
end
