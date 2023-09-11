using LinearAlgebra
using Combinatorics


# vertices = leaves. All other notes have degree 2. Inducibility density
# In "drawable" leaf order (not nice for flag algebras) 
struct BinaryTree
    isEmptyTree::Bool
    left::Union{BinaryTree,Nothing}
    right::Union{BinaryTree,Nothing}

    BinaryTree(left, right) = new(false, left, right)
    BinaryTree(isEmptyTree = true) = new(isEmptyTree, nothing, nothing)
end

# In any leaf order
struct BinaryTreeFlag <: Flag
    tree::BinaryTree
    perm::Vector{Int}

    BinaryTreeFlag(tree, perm) = begin
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
    BinaryTreeFlag(tree::BinaryTree) = new(tree, 1:size(tree))
    BinaryTreeFlag(isEmptyTree = true) =
        new(BinaryTree(isEmptyTree), isEmptyTree ? Int[] : Int[1])
end


# import Base.show
function Base.show(io::IO, T::BinaryTree)
    if T.isEmptyTree
        print(io, "o")
    elseif T.left === nothing && T.right === nothing
        print(io, "x")
    else
        print(io, "($(T.left)$(T.right))")
    end
end

function printTree(io::IO, T::BinaryTree, perm::Vector{Int})
    @assert size(T) == length(perm)
    if T.isEmptyTree
        print(io, "o")
    elseif T.left === nothing && T.right === nothing
        print(io, "$(perm[1])")
    else
        print(io, "(")
        printTree(io, T.left, perm[1:size(T.left)])
        # print(io, ")(")
        print(io, " ")
        printTree(io, T.right, perm[size(T.left)+1:end])
        print(io, ")")
    end
end

function Base.show(io::IO, T::BinaryTreeFlag)
    printTree(io, T.tree, T.perm)
end


function ==(A::BinaryTree, B::BinaryTree)
    A.isEmptyTree == B.isEmptyTree && A.left == B.left && A.right == B.right
end
function ==(A::BinaryTreeFlag, B::BinaryTreeFlag)
    A.tree == B.tree && A.perm == B.perm
end
function hash(A::BinaryTree, h::UInt)
    return hash(
        A.isEmptyTree,
        hash(A.right, hash(A.left, hash(:BinaryTree, h))) +
        hash(A.left, hash(A.right, hash(:BinaryTree, h))),
    )
end
function hash(A::BinaryTreeFlag, h::UInt)
    return hash(A.tree, hash(A.perm, hash(:BinaryTreeFlag, h)))
end

function permute(F::BinaryTreeFlag, p::AbstractVector{Int})
    return BinaryTreeFlag(F.tree, p[F.perm])
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

    p = vcat(p, 1:minimum(vcat([size(g1) + size(g2)], p))-1)

    trees = filter!(
        x -> size(x) == length(p),
        generateAll(BinaryTree, length(p), [1]; upToIso = true),
    )


    resLock = ReentrantLock()

    Threads.@threads for c in collect(combinations(1:length(p), size(g1)))
        q = zeros(Int, length(p))
        for q1 in SymmetricGroup(size(g1))

            @views q[p[1:size(g1)]] .= c[q1.d]

            for t in trees
                @views if g1 == subFlag(t, c[q1.d])
                    for q2 in SymmetricGroup(length(p) - size(g1))

                        @views q[setdiff(1:length(p), p[1:size(g1)])] .=
                            setdiff(1:length(p), c)[q2.d]

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
        factorial(size(r)) // (aut(r).size * factorial(length(p))) * BinaryTreeFlag(r) for
        r in res
    )
end

# TODO: precompute all products at once 

treeGlueDict::Dict{
    Tuple{BinaryTree,BinaryTree,AbstractVector{Int}},
    Union{Nothing,QuantumFlag{BinaryTreeFlag,Rational{Int64}}},
} = Dict{
    Tuple{BinaryTree,BinaryTree,AbstractVector{Int}},
    Union{Nothing,QuantumFlag{BinaryTreeFlag,Rational{Int64}}},
}()

function glue(g1::BinaryTree, g2::BinaryTree, p::AbstractVector{Int})

    get!(treeGlueDict, (g1, g2, p)) do
        glueNoDict(g1, g2, p)
    end

end

function generateAll(
    ::Type{BinaryTree},
    maxVertices::Int,
    maxPredicates::Vector{Int} = [1];
    upToIso = true,
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
    for k = 2:maxVertices
        treesK = vcat(attachAllWays.(trees[k-1])...)
        if upToIso
            push!(trees, unique(label.(treesK)))
        else
            push!(trees, unique(treesK))
        end
    end

    return vcat([BinaryTree()], trees...)

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

function aut(F::BinaryTree)

    if F.left === nothing && F.right === nothing
        if F.isEmptyTree
            return (gen = Vector{Int}[Int[]], size = 1)
        else
            return (gen = Vector{Int}[Int[1]], size = 1)
        end
    end

    leftAut = aut(F.left)
    if leftAut.size == 1
        empty!(leftAut.gen)
    end
    ln = size(F.left)

    if F.left === F.right
        return (
            gen = vcat([vcat(g, ln+1:2*ln) for g in leftAut.gen], [vcat(ln+1:2*ln, 1:ln)]),
            size = 2 * (leftAut.size^2),
        )
    else
        rightAut = aut(F.right)
        if rightAut.size == 1
            empty!(rightAut.gen)
        end
        return (
            gen = vcat(
                [vcat(g, ln+1:ln+size(F.right)) for g in leftAut.gen],
                [vcat(1:ln, c .+ ln) for c in rightAut.gen],
            ),
            size = leftAut.size * rightAut.size,
        )
    end
end

function aut(F::BinaryTreeFlag)

    automs = aut(F.tree)

    return (gen = [F.perm[g] for g in automs.gen], size = automs.size)
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
    return [false for i = 1:size(F)]
end

function labelCanonically(F::BinaryTree)::BinaryTree
    return label(F)
end

function maxPredicateArguments(::Type{BinaryTreeFlag})
    return 2
end

function joinLevel(T::BinaryTreeFlag, v::Int, w::Int)
    v == w && return 0

    leftVerts = T.perm[1:size(T.tree.left)]
    rightVerts = T.perm[size(T.tree.left)+1:end]
    if (v in leftVerts) && (w in leftVerts)
        return joinLevel(BinaryTreeFlag(T.tree.left, leftVerts), v, w) + 1
    elseif !(v in leftVerts) && !(w in leftVerts)
        return joinLevel(BinaryTreeFlag(T.tree.right, rightVerts), v, w) + 1
    end
    return 1
end

function distinguish(T::BinaryTreeFlag, v::Int, W::BitVector)
    return sort!([joinLevel(T, v, w) for w in findall(W)])
end