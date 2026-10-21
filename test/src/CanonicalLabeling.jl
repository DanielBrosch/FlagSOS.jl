using FlagSOS, Test
using Random, LinearAlgebra
using FlagSOS: combinations, permutations

function check_label(F; permutations_to_check=permutations(1:size(F)), kwargs...)
    original = deepcopy(F)
    canonical, canonical_group, group, p = FlagSOS.label(F; removeIsolated=false, kwargs...)
    @test F == original
    @test isperm(p)
    @test canonical == permute(F, p)
    @test FlagSOS.label(canonical; removeIsolated=false, kwargs...)[1] == canonical
    @test FlagSOS.label(F; prune=false, removeIsolated=false, kwargs...)[1] == canonical

    expected = Set(Tuple(q) for q in permutations_to_check if permute(F, q) == F)
    @test Set(Tuple(q) for q in group) == expected
    @test FlagSOS.order(group) == length(expected)
    @test FlagSOS.order(canonical_group) == length(expected)
    @test all(permute(canonical, q) == canonical for q in canonical_group)
    @test Set(Tuple(p[q[invperm(p)]]) for q in group) ==
          Set(Tuple(q) for q in canonical_group)
    for q in permutations_to_check
        @test FlagSOS.label(permute(F, q); removeIsolated=false, kwargs...)[1] == canonical
    end
    return canonical
end

function graph_from_mask(n, mask)
    A = falses(n, n)
    for (i, (u, v)) in enumerate(combinations(1:n, 2))
        A[u, v] = A[v, u] = !iszero(mask & (1 << (i - 1)))
    end
    return Graph(A)
end

# This object deliberately does not subtype Flag. The labeler must use only its
# oracles, including when the signatures carry no information at all.
struct OracleObject{mode}
    graph::Graph
    colors::Vector{Int}
end
Base.size(F::OracleObject) = size(F.graph)
Base.:(==)(F::OracleObject, G::OracleObject) = F.graph == G.graph && F.colors == G.colors
Base.hash(F::OracleObject{mode}, h::UInt) where {mode} =
    mode == :collision ? h : hash(F.graph, hash(F.colors, h))
FlagSOS.vertexColor(F::OracleObject, v::Int) = F.colors[v]
FlagSOS.permute(F::OracleObject{mode}, p::AbstractVector{Int}) where {mode} =
    OracleObject{mode}(permute(F.graph, p), F.colors[invperm(p)])
function FlagSOS.distinguish(F::OracleObject{mode}, v::Int, W::BitVector)::UInt where {mode}
    mode == :nonadditive && return UInt(count(F.graph.A[v, W]) >= 2)
    return zero(UInt)
end

@testset "All small graphs and automorphism groups" begin
    for n in 0:4
        canonical = Set{Graph}()
        for mask in 0:(2^binomial(n, 2) - 1)
            push!(canonical, check_label(graph_from_mask(n, mask)))
        end
        @test length(canonical) == (1, 1, 2, 4, 11)[n + 1]
    end
    # Five vertices exercise deeper stabilizers and nontrivial backjumps.
    canonical = Set{Graph}()
    for mask in 0:(2^10 - 1)
        F = graph_from_mask(5, mask)
        C, _, group, _ = FlagSOS.label(F; removeIsolated=false)
        push!(canonical, C)
        @test FlagSOS.label(F; prune=false, removeIsolated=false)[1] == C
        @test FlagSOS.order(group) == count(p -> permute(F, p) == F, permutations(1:5))
        @test FlagSOS.label(permute(F, [5, 3, 1, 4, 2]); removeIsolated=false)[1] == C
    end
    @test length(canonical) == 34
end

@testset "Other objects and wrappers" begin
    for mask in 0:26
        A = falses(3, 3)
        digits = mask
        for (u, v) in combinations(1:3, 2)
            edge = digits % 3
            digits ÷= 3
            A[u, v], A[v, u] = edge == 1, edge == 2
        end
        check_label(DirectedGraph(A))
    end
    for mask in 0:15
        edges = collect(combinations(1:4, 3))
        A = falses(count_ones(mask), 4)
        row = 0
        for (i, edge) in enumerate(edges)
            if !iszero(mask & (1 << (i - 1)))
                row += 1
                A[row, edge] .= true
            end
        end
        check_label(Hypergraph{3}(A))
    end
    cycle = Graph(Bool[0 1 0 1; 1 0 1 0; 0 1 0 1; 1 0 1 0])
    check_label(PartiallyColoredFlag(cycle; c=Dict(1 => 7, 3 => 7, 2 => 20)))
    for k in 0:4
        fixed_permutations = [vcat(collect(1:k), p) for p in permutations((k + 1):4)]
        check_label(PartiallyLabeledFlag(cycle, k); permutations_to_check=fixed_permutations)
        check_label(PartiallyLabeledFlag(InducedFlag{Graph,true}(cycle), k);
                    permutations_to_check=fixed_permutations)
    end
    check_label(ProductFlag((cycle, graph_from_mask(4, 13))))
    check_label(EdgeColoredGraph{2,false}([0 1 2 0; 1 0 1 2; 2 1 0 1; 0 2 1 0]))
    check_label(EdgeColoredGraph{2,true}([0 1 2 0; 1 0 1 2; 2 1 0 1; 0 2 1 0]))
    check_label(FlagSOS.EdgeMarkedFlag{Graph}(cycle, [FlagSOS.EdgePredicate(1, 3)]))
    check_label(SymmetricFunction([2, 1, 2, 1]))
    check_label(ConstantWeightCode{3,4}(Bool[1 1 1 0 0; 1 0 0 1 1]))
    leaf = BinaryTree(false)
    tree = labelCanonically(BinaryTree(leaf, BinaryTree(leaf, leaf)))
    check_label(BinaryTreeFlag(tree))
    check_label(FreeVariable(3))
end

@testset "Oracle refinement" begin
    for mask in (0, 1, 13, 30, 63)
        for mode in (:weak, :nonadditive)
            check_label(OracleObject{mode}(graph_from_mask(4, mask), [10, 10, -3, -3]))
        end
        check_label(OracleObject{:weak}(graph_from_mask(4, mask), ones(Int, 4)))
    end
    # All initial cells must be processed, even if the first cell does not split
    # anything. Test equitability for a nonlinear oracle over many partitions.
    for mask in 0:(2^10 - 1)
        F = OracleObject{:nonadditive}(graph_from_mask(5, mask), [1, 1, 2, 2, 2])
        colors = copy(F.colors)
        FlagSOS.refine!(colors, F, 0)
        for cell in unique(colors), splitter in unique(colors)
            signatures = [FlagSOS.distinguish(F, v, colors .== splitter)
                          for v in findall(==(cell), colors)]
            @test allequal(signatures)
        end
    end
    @test_throws DimensionMismatch FlagSOS.refine!([1], graph_from_mask(2, 1), 0)
    @test_throws ArgumentError FlagSOS.refine!([1, 2], graph_from_mask(2, 1), 1)

    F = OracleObject{:collision}(graph_from_mask(4, 13), ones(Int, 4))
    @test_throws ArgumentError FlagSOS.label(F; removeIsolated=false)
    check_label(F; canonicalKey=F -> Tuple(vec(Matrix(F.graph.A))))
end

@testset "Isolated vertices and concurrent calls" begin
    empty_result = FlagSOS.label(Graph())
    @test empty_result[4] isa Vector{Int}
    @test isempty(empty_result[4])
    for n in 1:5
        F = Graph(falses(n, n))
        @test size(FlagSOS.label(F)[1]) == 0
        @test FlagSOS.order(FlagSOS.label(F; removeIsolated=false)[3]) == factorial(n)
    end
    F = graph_from_mask(4, 1)
    @test size(FlagSOS.label(F)[1]) == 2
    @test size(FlagSOS.label(InducedFlag{Graph,true}(F))[1]) == 4
    fixtures = [graph_from_mask(5, mask) for mask in 0:63]
    serial = [FlagSOS.label(F; removeIsolated=false)[1] for F in fixtures]
    tasks = [Threads.@spawn FlagSOS.label(F; removeIsolated=false)[1] for F in fixtures]
    @test fetch.(tasks) == serial
end

# Avoid enumerating large groups. A subgroup of the known full order, whose
# generators all preserve the object, is the entire automorphism group.
function check_large_label(F, expected_order; trials=12, fixed=0, unpruned=false)
    rng = MersenneTwister(0x1abe1)
    n = size(F)
    original = deepcopy(F)
    canonical = FlagSOS.label(F; removeIsolated=false)[1]
    @test FlagSOS.label(canonical; removeIsolated=false)[1] == canonical
    if unpruned
        C, _, G, _ = FlagSOS.label(F; prune=false, removeIsolated=false)
        @test C == canonical
        @test FlagSOS.order(G) == expected_order
    end
    for trial in 1:trials
        tail = collect((fixed + 1):n)
        trial == 2 && reverse!(tail)
        trial > 2 && shuffle!(rng, tail)
        q = vcat(collect(1:fixed), tail)
        relabeled = permute(F, q)
        C, canonical_group, group, p = FlagSOS.label(relabeled; removeIsolated=false)
        @test C == canonical
        @test isperm(p)
        @test p[1:fixed] == 1:fixed
        @test permute(relabeled, p) == C
        @test permute(F, p[q]) == C
        @test FlagSOS.order(group) == expected_order
        @test FlagSOS.order(canonical_group) == expected_order
        @test all(isperm(g) && permute(relabeled, g) == relabeled for g in FlagSOS.SGS(group))
        @test all(isperm(g) && permute(C, g) == C for g in FlagSOS.SGS(canonical_group))
        # Membership sifts its argument in place, so pass fresh permutations.
        @test all(p[g[invperm(p)]] in canonical_group for g in group.gen)
        @test all(invperm(p)[g[p]] in group for g in canonical_group.gen)
    end
    @test F == original
    return canonical
end

function cycle_graph(n)
    A = falses(n, n)
    for i in 1:n
        j = mod1(i + 1, n)
        A[i, j] = A[j, i] = true
    end
    return Graph(A)
end

function incidence_matrix(n, edges)
    A = falses(length(edges), n)
    for (i, edge) in enumerate(edges)
        A[i, collect(edge)] .= true
    end
    return A
end

# Points and lines of PG(2,q), for prime q. Normalize the first nonzero
# coordinate to 1; incidence is the vanishing of the dot product modulo q.
function projective_plane_code(q)
    points = [x for x in Iterators.product(0:(q - 1), 0:(q - 1), 0:(q - 1))
              if any(!iszero, x) && x[findfirst(!iszero, x)] == 1]
    A = BitMatrix([sum(x .* y) % q == 0 for x in points, y in points])
    @test size(A) == (q^2 + q + 1, q^2 + q + 1)
    @test all(==(q + 1), sum(A; dims=2))
    intersections = Int.(A) * transpose(Int.(A))
    @test all(i == j || intersections[i, j] == 1 for i in axes(A, 1), j in axes(A, 1))
    return ConstantWeightCode{q + 1,2q}(A)
end

@testset "Larger graphs with known automorphism groups" begin
    @testset "Cycles, cliques, bipartite graphs, and repeated components" begin
        check_large_label(cycle_graph(24), 48)
        check_large_label(Graph(.!Matrix{Bool}(I, 12, 12)), factorial(12))
        bipartite = Graph(Bool[(i <= 6) != (j <= 6) for i in 1:12, j in 1:12])
        check_large_label(bipartite, 2 * factorial(6)^2)
        colored = PartiallyColoredFlag(bipartite;
            c=Dict(i => (i <= 6 ? 10 : 30) for i in 1:12))
        check_large_label(colored, factorial(6)^2)
        check_large_label(Graph(BitMatrix(kron(Matrix{Bool}(I, 3, 3), Matrix(cycle_graph(5).A)))),
                          factorial(3) * 10^3)
        # Every coordinate flip and coordinate permutation acts on the cube.
        cube = Graph(Bool[count_ones(xor(i, j)) == 1 for i in 0:31, j in 0:31])
        check_large_label(cube, 2^5 * factorial(5))
        check_large_label(PartiallyLabeledFlag(cycle_graph(24), 1), 2; fixed=1)
        check_large_label(PartiallyLabeledFlag(cycle_graph(24), 2), 1; fixed=2)
        # A rigid tree: the unique degree-3 vertex has arms of lengths 1, 2, 8.
        A = falses(12, 12)
        for (u, v) in ((1, 2), (1, 3), (3, 4), (1, 5), ((i, i + 1) for i in 5:11)...)
            A[u, v] = A[v, u] = true
        end
        check_large_label(Graph(A), 1; unpruned=true)
    end

    @testset "Same strongly regular parameters, different isomorphism classes" begin
        # Both graphs have parameters (16,6,2,2), so degree refinement alone
        # cannot separate them. Aut(rook) = (S4 x S4) ⋊ C2.
        # Shrikhande's group order: https://aeb.win.tue.nl/drg/graphs/Shrikhande.html
        points = collect(Iterators.product(0:3, 0:3))[:]
        rook = Graph(Bool[x != y && (x[1] == y[1] || x[2] == y[2]) for x in points, y in points])
        steps = ((1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3))
        shrikhande = Graph(Bool[(mod(x[1] - y[1], 4), mod(x[2] - y[2], 4)) in steps
                               for x in points, y in points])
        R = check_large_label(rook, 2 * factorial(4)^2; unpruned=true)
        S = check_large_label(shrikhande, 192; unpruned=true)
        @test R != S
        for F in (rook, shrikhande)
            colors = ones(Int, 16)
            FlagSOS.refine!(colors, F, 0)
            @test allequal(colors)
        end
    end
end

@testset "Larger objects using other oracles" begin
    @testset "Directed and product graphs" begin
        directed = DirectedGraph(Bool[j == mod1(i + 1, 17) for i in 1:17, j in 1:17])
        check_large_label(directed, 17; unpruned=true)
        check_large_label(DirectedGraph(Bool[i < j for i in 1:16, j in 1:16]), 1)
        # Alternating edge colors preserve half of the dihedral group.
        A = zeros(Int, 16, 16)
        for i in 1:16
            j = mod1(i + 1, 16)
            A[i, j] = A[j, i] = isodd(i) ? 1 : 2
        end
        check_large_label(EdgeColoredGraph{2,false}(A), 16)
        check_large_label(EdgeColoredGraph{2,true}(copy(A)), 32)
        check_large_label(ProductFlag((Graph(A .== 1), Graph(A .== 2))), 16)
    end

    @testset "Hypergraphs and constant-weight codes" begin
        for q in (2, 3)
            # Over a prime field the full group is PGL(3,q).
            group_order = ((q^3 - 1) * (q^3 - q) * (q^3 - q^2)) ÷ (q - 1)
            check_large_label(projective_plane_code(q), group_order)
        end
        matching = ConstantWeightCode{3,6}(incidence_matrix(12, [1:3, 4:6, 7:9, 10:12]))
        check_large_label(matching, factorial(3)^4 * factorial(4))
        complete = Hypergraph{3}(incidence_matrix(8, collect(combinations(1:8, 3))))
        check_large_label(complete, factorial(8))
        # Duplicate exponent classes exercise unary rather than relational data.
        check_large_label(SymmetricFunction(repeat([1, 3, 7]; inner=4)), factorial(4)^3)
    end

    @testset "Binary trees with different stabilizer chains" begin
        balanced = BinaryTree(false)
        for _ in 1:3
            balanced = BinaryTree(balanced, balanced)
        end
        # One independent swap at each of the seven internal nodes.
        check_large_label(BinaryTreeFlag(labelCanonically(balanced)), 2^7; trials=6)
        caterpillar = BinaryTree(false)
        for _ in 2:12
            caterpillar = BinaryTree(BinaryTree(false), caterpillar)
        end
        # Only the terminal cherry can be swapped.
        check_large_label(BinaryTreeFlag(labelCanonically(caterpillar)), 2; trials=6)
    end

    @testset "Weak signatures and exact keys on a larger search tree" begin
        F = OracleObject{:collision}(cycle_graph(7), ones(Int, 7))
        # Exhaust all 7! permutations independently; a constant oracle makes all
        # refinement traces equal, so the exact key really decides the result.
        key(F) = Tuple(vec(Matrix(F.graph.A)))
        expected = maximum(key(permute(F, p)) for p in permutations(1:7))
        for prune in (false, true)
            C, _, G, _ = FlagSOS.label(F; removeIsolated=false, prune, canonicalKey=key)
            @test key(C) == expected
            @test FlagSOS.order(G) == 14
        end
    end
end
