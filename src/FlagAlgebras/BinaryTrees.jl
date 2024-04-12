using LinearAlgebra
using Combinatorics
using ProgressMeter

export BinaryTree, BinaryTreeFlag



# vertices = leaves. All other notes have degree 2. Inducibility density
# In "drawable" leaf order (not nice for flag algebras) 
struct BinaryTree
    isEmptyTree::Bool
    left::Union{BinaryTree,Nothing}
    right::Union{BinaryTree,Nothing}

    BinaryTree(left, right) = new(false, left, right)
    BinaryTree(isEmptyTree=true) = new(isEmptyTree, nothing, nothing)
end

function treeFactor(T)
    # @show T
    if T isa PartiallyLabeledFlag
        return factorial(size(T) - T.n) // aut(T).size
    else
        return factorial(size(T)) // aut(T).size

    end
end
# In any leaf order
struct BinaryTreeFlag <: Flag
    tree::BinaryTree
    perm::Vector{Int}

    function BinaryTreeFlag(tree, perm)
        # @show tree 
        # @show labelCanonically(tree)
        @assert tree === labelCanonically(tree)
        # treeL, p = labelPerm(tree)
        # tree = treeL 
        # pInv = [findfirst(x->x==i, p) for i = 1:maximum(p; init = 0)]
        # perm = perm[pInv]
        @assert size(tree) == length(perm)
        auts = aut(tree)

        if auts.size <= 1 || perm == 1:size(tree)
            return new(tree, perm)
        end

        fullgroup = generateGroup(AbstractAlgebra.perm.(auts.gen), auts.size)

        perm2 = copy(perm)
        for p in fullgroup
            pNew = perm[p.d]
            if pNew < perm2
                perm2 = pNew
            end
        end
        return new(tree, perm2)
    end
    BinaryTreeFlag(tree::BinaryTree) = BinaryTreeFlag(tree, 1:size(tree))
    function BinaryTreeFlag(isEmptyTree=true)
        return new(BinaryTree(isEmptyTree), isEmptyTree ? Int[] : Int[1])
    end
end

# import Base.show
function Base.show(io::IO, T::BinaryTree)
    if T.isEmptyTree
        print(io, "∅")
    elseif T.left === nothing && T.right === nothing
        print(io, "•")
    else
        print(io, "($(T.left)$(T.right))")
    end
end


function printTree(io::IO, T::BinaryTree, perm::Vector)
    @assert size(T) == length(perm)
    if T.isEmptyTree
        print(io, "∅")
    elseif T.left === nothing && T.right === nothing
        print(io, "$(perm[1])")
    else
        print(io, "(")
        printTree(io, T.left, perm[1:size(T.left)])
        # print(io, ")(")
        print(io, "")
        printTree(io, T.right, perm[(size(T.left)+1):end])
        print(io, ")")
    end
end

function Base.show(io::IO, T::BinaryTreeFlag)
    if T.perm == 1:size(T)
        return show(io, T.tree)
    end
    return printTree(io, T.tree, T.perm)
    # end
end

function Base.show(io::IO, T::PartiallyLabeledFlag{BinaryTreeFlag})
    p = convert(Vector{Union{Int64,String}}, T.F.perm)
    p[p.>T.n] .= "•"
    return printTree(io, T.F.tree, p)
end


function printTreeLatex(T::BinaryTree, labels=["" for _ in 1:size(T)])

    function printForestTreeInner(S, labels)
        if S.left === nothing
            if labels[1] == ""
                return "[, treeNode] "
            else
                return "[$(labels[1]), treeNodeLabeled] "
            end
        else
            r = "[, treeNodeInner "
            r *= printForestTreeInner(S.left, labels[1:size(S.left)])
            r *= printForestTreeInner(S.right, labels[size(S.left)+1:end])
            r *= "] "
            return r
        end
    end

    # res = "\\begin{alone}\n"
    res = "\\begin{forest}\n"
    res *= "[, treeNodeRoot "
    if T.left !== nothing
        res *= printForestTreeInner(T.left, labels[1:size(T.left)])
        res *= printForestTreeInner(T.right, labels[size(T.left)+1:end])
    end
    res *= "]\n"
    res *= "\\end{forest}\n"
    # res *= "\\end{alone}\n"
    res
end

function printTreeLatex(T::BinaryTreeFlag, labels=["" for p in T.perm])
    return printTreeLatex(T.tree, labels)
end

function printTreeLatex(T::PartiallyLabeledFlag{BinaryTreeFlag}, labels=[p <= T.n ? "$p" : "" for p in T.F.perm])
    return printTreeLatex(T.F.tree, labels)
end

function ==(A::BinaryTree, B::BinaryTree)
    return A.isEmptyTree == B.isEmptyTree && (A.left == B.left && A.right == B.right)
    # return A.isEmptyTree == B.isEmptyTree && ((A.left == B.left && A.right == B.right) || (A.left == B.right && A.right == B.left))
end
function ==(A::BinaryTreeFlag, B::BinaryTreeFlag)
    if size(A) <= 1 || size(B) <= 1
        return size(B) == size(A) && A.perm == B.perm
    end
    return A.tree == B.tree && A.perm == B.perm
    # ALeft = BinaryTreeFlag(A.tree.left, A.perm[1:size(A.tree.left)])
    # ARight = BinaryTreeFlag(A.tree.right, A.perm[(size(A.tree.left)+1):end])
    # BLeft = BinaryTreeFlag(B.tree.left, B.perm[1:size(B.tree.left)])
    # BRight = BinaryTreeFlag(B.tree.right, B.perm[(size(B.tree.left)+1):end])
    # return (ALeft == BLeft && ARight == BRight) ||(ALeft == BRight && ARight == BLeft) 
end
function hash(A::BinaryTree, h::UInt)
    return hash(
        A.isEmptyTree,
        hash(A.right, hash(A.left, hash(:BinaryTree, h))) +
        hash(A.left, hash(A.right, hash(:BinaryTree, h))),
    )
end
function hash(A::BinaryTreeFlag, h::UInt)
    # if size(A) <= 1
    # end
    return hash(A.tree, hash(A.perm, hash(:BinaryTreeFlag, h)))

    # ALeft = BinaryTreeFlag(A.tree.left, A.perm[1:size(A.tree.left)])
    # ARight = BinaryTreeFlag(A.tree.right, A.perm[(size(A.tree.left)+1):end])
    # return hash(ALeft, hash(:BinaryTree, h)) + hash(ARight, hash(:BinaryTree, h))
end

function permute(F::BinaryTreeFlag, p::AbstractVector{Int})
    if size(F) == 0 && length(p) > 0 && p[1] == 1
        return BinaryTreeFlag(BinaryTree(false))
    end

    # @show F, F.perm, p
    # @show [p[i] for i in F.perm]

    # return BinaryTreeFlag(F.tree, p[F.perm])
    # return BinaryTreeFlag(F.tree, [F.perm[i] for i in p])
    return BinaryTreeFlag(F.tree, [p[i] for i in F.perm])
end

Base.one(::Type{BinaryTree}) = BinaryTree()
Base.one(::Type{BinaryTreeFlag}) = BinaryTreeFlag()

function size(G::BinaryTree)::Int
    if G.isEmptyTree
        return 0
    end
    if G.left === nothing && G.right === nothing
        return 1
    end

    return size(G.left) + size(G.right)
end
function size(G::BinaryTreeFlag)::Int
    return size(G.tree)
end

function glueNoDict(g1::BinaryTree, g2::BinaryTree, p::AbstractVector{Int})
    @info "Glue no dict"
    @assert minimum(p[1:size(g1)]; init=size(g2) + 1) > size(g2)
    if g1 == BinaryTree() && g2 == BinaryTree()
        return 1 // 1 * BinaryTreeFlag(g1)
    end

    if g1 == BinaryTree() || g2 == BinaryTree()
        if g1 == BinaryTree()
            return 1 // 1 * BinaryTreeFlag(g2)
        else
            return 1 // 1 * BinaryTreeFlag(g1)
        end
    end

    res = []

    p = vcat(p, 1:(minimum(vcat([size(g1) + size(g2)], p))-1))

    trees = filter!(
        x -> size(x) == length(p), generateAll(BinaryTree, length(p), [1]; upToIso=true)
    )

    resLock = ReentrantLock()

    Threads.@threads for c in collect(combinations(1:length(p), size(g1)))
        q = zeros(Int, length(p))
        for q1 in SymmetricGroup(size(g1))
            @views q[p[1:size(g1)]] .= c[q1.d]

            for t in trees
                @views if g1 == subFlag(t, c[q1.d])
                    for q2 in SymmetricGroup(length(p) - size(g1))
                        @views q[setdiff(1:length(p), p[1:size(g1)])] .= setdiff(
                            1:length(p), c
                        )[q2.d]

                        @views if g2 == subFlag(t, q[1:size(g2)])
                            t2 = label(t)
                            lock(resLock) do
                                push!(res, t2)
                            end
                        end
                    end
                end
            end
        end
    end

    m = length(res)

    if m == 0
        return nothing
    end

    return sum(
        # treeFactor(r) // factorial(length(p)) * BinaryTreeFlag(r) for r in res
        # 1//treeFactor(r)*
        # treeFactor(r)//factorial(length(p))*BinaryTreeFlag(r) for r in res
        # treeFactor(r)//(treeFactor(g1)*treeFactor(g2)*factorial(length(p)))*
        # BinaryTreeFlag(r) for r in res
        treeFactor(g1) * treeFactor(g2) // factorial(length(p)) * BinaryTreeFlag(r) for r in res
        # treeFactor(r)//factorial(length(p))*BinaryTreeFlag(r) for r in res
    )
end

function glue(g1::BinaryTreeFlag, g2::BinaryTreeFlag, p::AbstractVector{Int})
    if size(g1) == 0 && size(g2) == 0 && length(p) > 0 && p[1] == 1
        return BinaryTreeFlag(BinaryTree(false))
    end

    # p2 = p[g1.perm]
    # @show g1 
    # @show g2 
    # @show p
    tmp = p[g1.perm]
    p2 = vcat(tmp, setdiff(p, tmp))
    p3 = Int[(i in g2.perm ? findfirst(x -> x == i, g2.perm) : i) for i in p2]
    # p2 = [i in  for i in p]
    @assert !issorted(g1.perm) || !issorted(g2.perm) || p3 == p
    @views sort!(p3[p3.>size(g2)])
    @views sort!(p3[size(g1)+1:end])
    @assert issorted(p3[p3.>size(g2)]) "$(g1.tree) $(g2.tree) $p3"
    return glue(g1.tree, g2.tree, p3)
    # return glueNoDict(g1.tree, g2.tree, p3)
end

# TODO: precompute all products at once 

treeGlueDict::Dict{Tuple{BinaryTree,BinaryTree,AbstractVector{Int}},Union{Nothing,QuantumFlag{BinaryTreeFlag,Rational{Int64}}}} = Dict{
    Tuple{BinaryTree,BinaryTree,AbstractVector{Int}},
    Union{Nothing,QuantumFlag{BinaryTreeFlag,Rational{Int64}}},
}()

function computeGlueDictC(n)
    trees = generateAll(BinaryTree, n, [1]; upToIso=true)
    # filter!(x -> size(x) == n, trees)
    @show trees

    # testDict = Dict{Tuple{BinaryTree,BinaryTree,Vector{Int64}},QuantumFlag{BinaryTreeFlag}}()

    treeDicts = Dict(
        T => Dict{Tuple{BinaryTree,BinaryTree,Vector{Int64}},Rational{Int}}() for T in trees
    )
    # threadDicts = Dict(i => Dict(T => [] for T in trees) for i = 1:Threads.nthreads())

    # @showprogress for T in trees[end-1:end-1]
    # @time Threads.@threads for T in trees

    numTrees = length(trees)

    p = Progress(numTrees; desc="Trees computed", barglyphs=BarGlyphs("[=> ]"))

    pTrees = [
        Progress(
            sum(binomial(size(T), i) for i in 0:size(T));
            desc="Tree $j",
            barglyphs=BarGlyphs("[=> ]"),
            enabled=false,
            offset=j,
        ) for (j, T) in enumerate(trees)
    ]

    progressChannel = Channel{Int}(Inf)
    dataChannel = Channel{Any}(Inf)

    makeDict = Threads.@spawn :interactive while true
        data = take!(dataChannel)
        if data === nothing
            @assert dataChannel.n_avail_items == 0
            break
        end

        mergewith!(mergewith!(+), treeDicts, data)
    end

    maxOffset = 20
    sem = Base.Semaphore(5)

    progressTask = Threads.@spawn :interactive while true
        if !isready(progressChannel)
            wait(progressChannel)
        end

        changed = false

        # !isready(progressChannel) && sleep(0.001)

        if isready(progressChannel)
            # while isready(progressChannel)
            # inds = collect(progressChannel)
            # println(length(inds))
            inds = Dict{Int,Int}()
            tStart = time()
            while isready(progressChannel)
                i = take!(progressChannel)
                inds[i] = get(inds, i, 0) + 1
                if time() - tStart > 1
                    break
                end
            end

            # display(length(inds))
            for (i, iCount) in inds
                # iCount = count(x->x==i, inds)
                # i = take!(progressChannel)
                # @show progressChannel.n_avail_items
                if i < 0
                    # @info "finished progress"
                    print(stdout, "\n")
                    return nothing
                    # break
                end
                if i == 0
                    next!(p; step=iCount)
                else
                    # changed = false
                    if !pTrees[i].enabled && pTrees[i].offset >= 0
                        pTrees[i].enabled = true
                        changed = true
                    else
                        # next!(pTrees[i])
                        pTrees[i].counter += iCount
                        if pTrees[i].n <= pTrees[i].counter
                            # ProgressMeter.lock_if_threading(pTrees[i]) do
                            # counter_changed = p.counter != counter
                            # p.counter = counter
                            # p.color = color

                            # @info "Really done with tree $i"

                            ProgressMeter.updateProgress!(pTrees[i]; ignore_predictor=true)
                            # end
                            pTrees[i].enabled = false
                            pTrees[i].offset = 1
                            pTrees[i].color = :red
                            changed = true
                            # ProgressMeter.updateProgress!(pTrees[i]; ignore_predictor=false)
                        end
                    end
                end
            end
        end

        # println("changed = $changed")
        treeOrder = []
        if changed
            c = 1
            for (i, pI) in enumerate(pTrees)
                if pI.enabled || pI.offset < 0
                    if c <= maxOffset
                        push!(treeOrder, i)
                        pI.offset = c
                        pI.enabled = true
                    else
                        pI.offset = -1
                        pI.enabled = false
                    end
                    c += 1
                    # ProgressMeter.lock_if_threading(pI) do
                    # counter_changed = p.counter != counter
                    # p.counter = counter
                    # p.color = color
                    ProgressMeter.updateProgress!(pI; ignore_predictor=true)
                    # end
                    # update!(pI)
                end
            end
            cMax = min(c, maxOffset)
            print(stdout, ("\n"^cMax) * "\r\u1b[K\u1b[A" * ("\r\u1b[A"^(cMax - 1)))
            if c > maxOffset
                print(
                    stdout,
                    ("\n"^(maxOffset + 1)) *
                    "And $(c-maxOffset) additional trees..." *
                    ("\r\u1b[A"^(maxOffset + 1)),
                )
            end
        end
    end

    bind(progressChannel, progressTask)

    Threads.@threads for (i, T) in collect(enumerate(trees))
        # Base.acquire(sem)
        # @show sem
        # @show sem.curr_cnt
        # @show sem.sem_size

        put!(progressChannel, i)
        m = size(T)
        k = factorial(size(T))

        # @show (i, T)

        Threads.@threads for c1 in
                             collect(Iterators.flatten(combinations(1:m, i) for i in 0:m))
            missingElements = setdiff(1:m, c1)

            treeDictsInner = Dict(
                T => Dict{Tuple{BinaryTree,BinaryTree,Vector{Int64}},Rational{Int}}() for
                T in trees
            )
            # @show c1
            tPerm = zeros(Int, m)
            pRes = zeros(Int, m)
            pResCopy = zeros(Int, m)

            overlapMin = max(2 * length(c1) - n, 0)
            # overlapMin = 0
            overlapMax = min(n + 2 * length(c1) - 2 * m, n)
            # overlapMax = min(overlapMin, overlapMax)

            # @show T, c1, overlapMin, overlapMax

            # overlapMin = 0
            # overlapMax = length(c1)

            # if overlapMin > overlapMax
            #     put!(progressChannel, i)
            #     continue
            # end

            # aLways allow overlap zero for quadratic modules
            ovRange = if overlapMin <= 0
                (overlapMin:max(0, overlapMax))
            else
                Iterators.flatten((0:0, overlapMin:overlapMax))
            end
            # ovRange = (overlapMin:overlapMax)

            # for overlap in Iterators.flatten(combinations(c1, i) for i = union([0],overlapMin:overlapMax))
            for overlap in Iterators.flatten(combinations(c1, i) for i in ovRange)
                c2 = sort!(union(overlap, missingElements))

                t1 = subFlag(T, c1)
                t2 = subFlag(T, c2)

                # @show (t1,t2)
                # gen1 = aut(t1)
                # gen2 = aut(t2)
                # automs1 = [p.d for p in generateGroup(perm.(gen1.gen), gen1.size)]
                # automs2 = [p.d for p in generateGroup(perm.(gen2.gen), gen2.size)]
                # automs1c = [c1[p] for p in automs1]
                # automs2c = [c2[p] for p in automs2]

                # joint1 = [p for p in automs1c if any([findfirst(x->x==i, p) for i in overlap] == [findfirst(x->x==i, q) for i in overlap] for q in automs2c)]
                # joint2 = [p for p in automs2c if any([findfirst(x->x==i, p) for i in overlap] == [findfirst(x->x==i, q) for i in overlap] for q in automs1c)]

                # # print(joint1) 
                # # print(joint2)
                # println((gen1.size, length(joint1), gen2.size, length(joint2)))

                t1l, t1p = labelPerm(t1)
                t2l, t2p = labelPerm(t2)

                # t1lFactor = treeFactor(t1l)
                # t2lFactor = treeFactor(t2l)

                # @show subFlag(BinaryTreeFlag(T), vcat(overlap, setdiff(c1, overlap)))
                # @show subFlag(BinaryTreeFlag(T), vcat(overlap, setdiff(c2, overlap)))
                # @show PartiallyLabeledFlag{BinaryTreeFlag}(subFlag(BinaryTreeFlag(T), vcat(overlap, setdiff(c1, overlap))); n = length(overlap))
                # @show PartiallyLabeledFlag{BinaryTreeFlag}(subFlag(BinaryTreeFlag(T), vcat(overlap, setdiff(c2, overlap))); n = length(overlap))

                pl1 = PartiallyLabeledFlag{BinaryTreeFlag}(subFlag(BinaryTreeFlag(T), vcat(overlap, setdiff(c1, overlap))); n=length(overlap))
                pl2 = PartiallyLabeledFlag{BinaryTreeFlag}(subFlag(BinaryTreeFlag(T), vcat(overlap, setdiff(c2, overlap))); n=length(overlap))
                @assert treeFactor(pl1) == treeFactor(labelCanonically(pl1))

                # @show pl2
                # @show treeFactor(pl2)
                # @show labelCanonically(pl2)
                # @show treeFactor(labelCanonically(pl2))

                # @assert treeFactor(pl2) == treeFactor(labelCanonically(pl2))

                t1lFactor = treeFactor(pl1)
                t2lFactor = treeFactor(pl2)

                # if length(overlap) == 0
                #     @show t1l
                #     @show pl1 
                #     @show treeFactor(t1l)
                #     @show t1lFactor 
                #     @show t2l
                #     @show pl2
                #     @show treeFactor(t2l)
                #     @show t2lFactor
                #     @show aut(t2l)
                #     @show aut(pl2)
                #     @show labelCanonically(pl2)
                #     @show aut(labelCanonically(pl2))
                #     @assert t1lFactor == treeFactor(t1l)
                #     @assert t2lFactor == treeFactor(t2l)
                # end

                # @show subFlag(T, vcat(overlap, setdiff(c1, overlap))
                # @show subFlag(T, vcat(overlap, setdiff(c2, overlap))
                # t1lFactor = treeFactor(PartiallyLabeledFlag{BinaryTreeFlag}(subFlag(T, vcat(overlap, setdiff(c1, overlap))), length(overlap)))
                # t2lFactor = treeFactor(PartiallyLabeledFlag{BinaryTreeFlag}(subFlag(T, vcat(overlap, setdiff(c2, overlap))), length(overlap)))

                # t1lFactor = 1 // 1
                # t2lFactor = 1 // 1


                # global t1test = t1

                # @assert t2l == subFlag(t2, t2p)

                # Generating all automorphisms of t1, t2
                genAutost1, genAutost2 = aut(t1l), aut(t2l)
                fullGroupt1 = generateGroup(perm.(genAutost1.gen), genAutost1.size)
                fullGroupt2 = generateGroup(perm.(genAutost2.gen), genAutost2.size)
                # fullGroupt2 = [AbstractAlgebra.perm(1:size(t2l))]
                # fullGroupt1 = [AbstractAlgebra.perm(1:size(t1l))]

                t1InTPerm = zeros(Int, length(c1))
                t1pInit = deepcopy(t1p)
                t2pInit = deepcopy(t2p)

                # @info "before"
                # overlapCoordc1 = [findfirst(x->x==i, c1) for i in overlap]
                # @show fullGroupt1
                # testA = length(fullGroupt1)
                # filter!(x->Set(x.d[overlapCoordc1]) != Set(overlapCoordc1) || x.d == 1:length(x.d),fullGroupt1)
                # testB = length(fullGroupt1)
                # @show testA, testB
                # overlapCoordc2 = [findfirst(x->x==i, c2) for i in overlap]
                # filter!(x->Set(x.d[overlapCoordc2]) != Set(overlapCoordc2) || x.d == 1:length(x.d),fullGroupt2)

                # tmp = []

                # jointAutoms = [(a1, a2) for a1 in fullGroupt1 for a2 in fullGroupt2 if ]

                # fullGroupt2Shifted = 

                # TODO: idea:
                # first swap positions in final permutation according to aut1
                # then numbers in final permutation according to aut2

                for autot1 in fullGroupt1
                    for autot2 in fullGroupt2

                        # tPerm .= 0

                        @views t1p .= t1pInit[autot1.d]
                        @views t2p .= t2pInit[autot2.d]
                        # t2p = t2pInit
                        # t2p = minimum(fullGroupt2) do p
                        # t2pInit[p.d]
                        # end

                        @views tPerm[1:size(t2)] .= c2[t2p] #1:size(t2)
                        @views tPerm[(size(t2)+1):m] .= setdiff(1:m, c2)

                        # t1InTPermB = [findfirst(x -> x == i, tPerm) for i in c1]

                        for (j, k) in enumerate(c1)
                            t1InTPerm[j] = findfirst(x -> x == k, tPerm)
                        end

                        # t1pInitInTPerm = minimum(fullGroupt1) do p
                        #     t1InTPerm[t1pInit[p.d]]
                        # end

                        # @assert t1InTPerm == t1InTPermB

                        # @show t1InTPerm
                        # @show tPerm

                        # Does t1p need to be inverted? (Probably no?!?!?)
                        # t1p = [findfirst(x->x==i, t1p) for i =1:length(t1p)]

                        # pResB = t1InTPerm[t1p]
                        # @show t1InTPerm, t1p, pResB
                        # pResB = Int.(vcat(pResB, setdiff(1:m, pResB)))

                        # pRes[1:length(t1p)] .= t1pInitInTPerm#t1InTPerm[t1p]
                        @views pRes[1:length(t1p)] .= t1InTPerm[t1p]
                        # pRes[length(t1p)+1:end] .= setdiff(1:m, t1pInitInTPerm)#t1InTPerm[t1p])
                        @views pRes[(length(t1p)+1):end] .= setdiff(1:m, t1InTPerm[t1p])

                        # @show pRes
                        # @show pResB
                        # @assert pRes == pResB "$pRes, $pResB"

                        t2n = length(c2)
                        rMin = deepcopy(pRes)
                        @views sort!(rMin[pRes.>t2n])
                        # for q in SymmetricGroup(length(setdiff(c1, c2)))
                        #     pResCopy .= pRes

                        #     if t2n < m && m > 0 && length(q.d) > 0
                        #         # @show q.d
                        #         @views pResCopy[pRes.>t2n] .= pRes[pRes.>t2n][q.d]
                        #     end

                        #     if pResCopy < rMin 
                        #         rMin .= pResCopy
                        #     end
                        # end
                        # rMin = minimum(SymmetricGroup(length(setdiff(c1, c2)))) do q
                        #     pResCopy = deepcopy(pRes)

                        #     if t2n < m && m > 0 && length(q.d) > 0
                        #         # @show q.d
                        #         pResCopy[pRes.>t2n] .= pRes[pRes.>t2n][q.d]
                        #     end
                        #     pResCopy
                        # end
                        # # @show rMin



                        treeDictsInner[T][(t1l, t2l, rMin)] =
                            get(treeDictsInner[T], (t1l, t2l, rMin), 0 // 1) +
                            t1lFactor * t2lFactor // k
                    end
                end
            end
            put!(progressChannel, i)
            put!(dataChannel, treeDictsInner)

            # yield()
        end
        # @info "done with tree $i"
        put!(progressChannel, 0)
        # Base.release(sem)
    end
    put!(progressChannel, -1)
    close(progressChannel)
    put!(dataChannel, nothing)

    # @info "Waiting for channel"
    wait(makeDict)


    treeGlueDictTmp::Dict{Tuple{BinaryTree,BinaryTree,AbstractVector{Int}},Union{Nothing,QuantumFlag{BinaryTreeFlag,Rational{Int64}}}} = Dict{
        Tuple{BinaryTree,BinaryTree,AbstractVector{Int}},
        Union{Nothing,QuantumFlag{BinaryTreeFlag,Rational{Int64}}},
    }()

    @showprogress 0.1 "turning results into flag combinations" for (T, tDict) in treeDicts
        for (p, c) in collect(tDict)
            # treeGlueDictTmp[p] = get!(treeGlueDictTmp, p, 0 // 1 * BinaryTreeFlag()) + treeFactor(T) * c * BinaryTreeFlag(T)
            treeGlueDictTmp[p] = get!(treeGlueDictTmp, p, 0 // 1 * BinaryTreeFlag()) + c * BinaryTreeFlag(T)
        end
    end

    for (p, c) in treeGlueDictTmp
        if haskey(treeGlueDict, p)
            @error "Computing $p double at $n"
        end
        treeGlueDict[p] = c
    end

    # @info "waiting for merging"
    # wait(makeDict)

    return treeGlueDict
end

function glue(g1::BinaryTree, g2::BinaryTree, p::AbstractVector{Int})
    if !haskey(treeGlueDict, (g1, g2, p))
        @show g1
        @show g2
        @show p
        @show n = 2 * max(size(g1), size(g2)) - length(intersect(p[1:size(g1)], 1:size(g2)))

        if n > maximum(p; init=0) && all(p[1:size(g1)] .> size(g2))
            # @assert all(p[1:size(g1)] .> size(g2))
            tmp = glueNoDict(g1, g2, p)
            treeGlueDict[(g1, g2, p)] = tmp
            return tmp
        end


        computeGlueDictC(n)#maximum(p; init=0))
        # computeGlueDictC(n)

        @assert haskey(treeGlueDict, (g1, g2, p)) "$n does not compute $((g1,g2,p))"
    end

    return treeGlueDict[(g1, g2, p)]

    # get!(treeGlueDict, (g1, g2, p)) do
    #     glueNoDict(g1, g2, p)
    # end
end

function generateAll(
    ::Type{BinaryTree},
    maxVertices::Int,
    maxPredicates::Vector{Int}=[1];
    upToIso=true,
    withProperty=(F::BinaryTreeFlag) -> true,
)
    function attachAllWays(t::BinaryTree)
        res = [BinaryTree(t, BinaryTree(false)), BinaryTree(BinaryTree(false), t)]
        if t.left === nothing
            return res
        end

        for t2 in attachAllWays(t.left)
            push!(res, BinaryTree(t2, t.right))
        end
        for t2 in attachAllWays(t.right)
            push!(res, BinaryTree(t.left, t2))
        end
        return res
    end

    trees = [[BinaryTree(false)]]
    for k in 2:maxVertices
        treesK = vcat(attachAllWays.(trees[k-1])...)
        if upToIso
            push!(trees, unique(label.(treesK)))
        else
            push!(trees, unique(treesK))
        end
    end

    return vcat([BinaryTree()], trees...)
end

function generateAll(
    ::Type{BinaryTreeFlag},
    maxVertices::Int,
    maxPredicates::Vector{Int}=[1];
    upToIso=true,
    withProperty=(F::BinaryTreeFlag) -> true,
)
    trees = generateAll(BinaryTree, maxVertices, maxPredicates; upToIso=upToIso)
    return [BinaryTreeFlag(T) for T in trees]
end

# check if swapping v1 and v2 leaves g invariant
function isSym(g::BinaryTree, v1::Int, v2::Int)::Bool
    vMin = min(v1, v2)
    vMax = max(v1, v2)

    if size(g) == 2 && vMin == 1 && vMax == 2
        return true
    end

    nl = size(g.left)

    if vMin <= nl
        if vMax > nl
            return false
        end
        return isSym(g.left, vMin, vMax)
    end
    if vMin > nl
        if vMax <= nl
            return false
        end
        return isSym(g.right, vMin - nl, vMax - nl)
    end
end

# check if swapping v1 and v2 leaves g invariant
function isSym(g::BinaryTreeFlag, v1::Int, v2::Int)::Bool
    v1p = findfirst(x -> x == v1, g.perm)
    v2p = findfirst(x -> x == v2, g.perm)

    return isSym(g.tree, v1p, v2p)
end

function subFlag(F::BinaryTree, vertices::AbstractVector{Int})
    if length(vertices) == 0
        return BinaryTree()
    end

    if F.left === nothing
        if vertices == [1]
            return F
        else
            return nothing
        end
    end

    leftVertices = [v for v in vertices if v <= size(F.left)]
    rightVertices = [v for v in vertices if v > size(F.left)]

    orderLeftRight = vertices == vcat(leftVertices, rightVertices)

    if !orderLeftRight && vertices != vcat(rightVertices, leftVertices)
        return nothing
    end

    rightVertices = rightVertices .- size(F.left)

    leftSub = subFlag(F.left, leftVertices)
    rightSub = subFlag(F.right, rightVertices)

    if leftSub === nothing || rightSub === nothing
        if length(leftVertices) == 0 && leftSub === nothing
            return rightSub
        elseif length(rightVertices) == 0 && rightSub === nothing
            return leftSub
        end
        return nothing
    else
        if size(leftSub) == 0
            return rightSub
        end
        if size(rightSub) == 0
            return leftSub
        end
        if orderLeftRight
            return BinaryTree(leftSub, rightSub)
        else
            return BinaryTree(rightSub, leftSub)
        end
    end
end


function subFlag(F::BinaryTreeFlag, vertices::AbstractVector{Int})

    # @show F 
    # @show vertices
    vertsPermed = Int[findfirst(x -> x == i, F.perm) for i in vertices]

    vertsOrdered = sort(vertsPermed)

    Fs = subFlag(F.tree, vertsOrdered)

    # @show vertsPermed
    for i = maximum(vertsPermed; init=0):-1:1
        if !in(i, vertsPermed)
            vertsPermed[vertsPermed.>i] .-= 1
        end
    end

    if length(vertsPermed) > 0
        vertsPermedInv = [findfirst(x -> x == i, vertsPermed) for i = 1:maximum(vertsPermed)]
    else
        vertsPermedInv = vertsPermed
    end

    # @show vertsPermed
    @assert sort(vertsPermed) == 1:size(Fs)

    FsL, pl = labelPerm(Fs)



    # return BinaryTreeFlag(Fs, vertsPermedInv)

    # @assert false "broken here?!"

    return BinaryTreeFlag(FsL, vertsPermedInv[pl])


end

function aut(F::BinaryTree)
    if F.left === nothing && F.right === nothing
        if F.isEmptyTree
            return (gen=Vector{Int}[Int[]], size=1)
        else
            return (gen=Vector{Int}[Int[1]], size=1)
        end
    end

    leftAut = aut(F.left)
    if leftAut.size == 1
        empty!(leftAut.gen)
    end
    ln = size(F.left)

    if F.left == F.right
        return (
            gen=vcat(
                [vcat(g, (ln+1):(2*ln)) for g in leftAut.gen],
                [vcat((ln+1):(2*ln), 1:ln)],
            ),
            size=2 * (leftAut.size^2),
        )
    else
        rightAut = aut(F.right)
        if rightAut.size == 1
            empty!(rightAut.gen)
        end
        return (
            gen=vcat(
                [vcat(g, (ln+1):(ln+size(F.right))) for g in leftAut.gen],
                [vcat(1:ln, c .+ ln) for c in rightAut.gen],
            ),
            size=leftAut.size * rightAut.size,
        )
    end
end

function aut(F::BinaryTreeFlag)
    # @show F 
    # @show F.tree
    # @show F.perm
    automs = aut(F.tree)
    # @show automs 

    permGen = []
    for g in automs.gen
        tmp = [F.perm[g[findfirst(x -> x == i, F.perm)]] for i in 1:size(F.perm, 1)]
        push!(permGen, tmp)
    end

    return (gen=permGen, size=automs.size)
    # return (gen=[F.perm[g] for g in automs.gen], size=automs.size)
    # return (gen=[g[F.perm] for g in automs.gen], size=automs.size)
    # return (gen=[F.perm[[findfirst(x->x==i, g) for i in 1:size(F.perm,1)]] for g in automs.gen], size=automs.size)
end

function label(F::BinaryTree)
    if F.left === nothing
        return F
    end
    if hash(F.left) < hash(F.right)
        return BinaryTree(label(F.left), label(F.right))
    else
        return BinaryTree(label(F.right), label(F.left))
    end
end

function labelPerm(F::BinaryTree)
    if size(F) == 0
        return F, Int[]
    end

    if F.left === nothing
        return F, [1]
    end

    leftLabel, leftPerm = labelPerm(F.left)
    rightLabel, rightPerm = labelPerm(F.right)

    if hash(F.left) < hash(F.right)
        p = vcat(leftPerm, rightPerm .+ length(leftPerm))
        return BinaryTree(leftLabel, rightLabel), p
    else
        p = vcat(rightPerm .+ length(leftPerm), leftPerm)
        return BinaryTree(rightLabel, leftLabel), p
    end
end

function countEdges(::BinaryTree)::Vector{Int}
    return 0
end
function countEdges(::BinaryTreeFlag)::Vector{Int}
    return 0
end

function isolatedVertices(F::BinaryTreeFlag)::BitVector
    return [false for i in 1:size(F)]
end

function labelCanonically(F::BinaryTree)::BinaryTree
    return label(F)
end

function labelCanonically(F::BinaryTreeFlag)::BinaryTreeFlag
    return BinaryTreeFlag(label(F.tree), 1:size(F.tree))
end

function maxPredicateArguments(::Type{BinaryTreeFlag})
    return 2
end

function joinLevel(T::BinaryTreeFlag, v::Int, w::Int)
    v == w && return 0

    leftVerts = T.perm[1:size(T.tree.left)]
    rightVerts = T.perm[(size(T.tree.left)+1):end]
    if (v in leftVerts) && (w in leftVerts)
        return joinLevel(BinaryTreeFlag(T.tree.left, leftVerts), v, w) + 1
    elseif !(v in leftVerts) && !(w in leftVerts)
        return joinLevel(BinaryTreeFlag(T.tree.right, rightVerts), v, w) + 1
    end
    return 1
end

function distinguish(T::BinaryTreeFlag, v::Int, W::BitVector)::UInt
    return hash(sort!([joinLevel(T, v, w) for w in findall(W)]))
end

function isInducedFlag(T::Type{BinaryTreeFlag})
    return true
end