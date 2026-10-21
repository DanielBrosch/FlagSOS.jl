using FlagSOS, Test
using FlagSOS: combinations, permutations

# Expectations below come from enumeration results or independent counting
# formulas, never from another invocation of the canonicalizer/generator.
# InducedFlag retains isolated vertices, so each size is an exact vertex count.
function check_size_counts(flags, expected)
    @test length(flags) == sum(expected)
    @test length(Set(flags)) == length(flags)
    @test issorted(size.(flags))
    @test [count(F -> size(F) == n, flags) for n in 0:(length(expected) - 1)] == expected
    @test all(F -> labelCanonically(F) == F, flags)
end

function check_labeled_mass(flags, n, expected; fixed=0)
    total = big(0)
    for F in flags
        size(F) == n || continue
        group = FlagSOS.label(F; removeIsolated=false)[3]
        @test all(isperm(g) && permute(F, g) == F for g in group.gen)
        quotient, remainder = divrem(factorial(big(n - fixed)), FlagSOS.order(group))
        @test remainder == 0
        total += quotient
    end
    # Orbit-stabilizer: the sum of orbit sizes must recover every labeled object.
    @test total == expected
end

# Burnside on the action of S_n on the unordered pairs. For two interchangeable
# edge colors, average also over their swap (nonedges remain fixed). Along an
# odd edge cycle only a nonedge survives the swap; an even cycle has 3 choices.
function edge_color_count(n; colorblind=false)
    edges = [Tuple(e) for e in combinations(1:n, 2)]
    edge_index = Dict(e => i for (i, e) in enumerate(edges))
    total = 0
    for p in permutations(1:n)
        action = [edge_index[minmax(p[u], p[v])] for (u, v) in edges]
        visited = falses(length(edges))
        lengths = Int[]
        for i in eachindex(edges)
            visited[i] && continue
            j, len = i, 0
            while !visited[j]
                visited[j] = true
                len += 1
                j = action[j]
            end
            push!(lengths, len)
        end
        total += 3^length(lengths)
        colorblind && (total += 3^count(iseven, lengths))
    end
    return total ÷ (factorial(n) * (colorblind ? 2 : 1))
end

function maximal_triple_system(F)
    n = size(F)
    A = F.F.A
    covered = falses(n, n)
    for row in axes(A, 1), (u, v) in combinations(findall(@view(A[row, :])), 2)
        covered[u, v] = covered[v, u] = true
    end
    return !any(!covered[u, v] && !covered[u, w] && !covered[v, w]
                for (u, v, w) in combinations(1:n, 3))
end

@testset "Known enumeration counts" begin
    # Release cached generated objects after this suite, including on failure.
    FlagSOS.Memoization.empty_cache!(generateAll)
    try
        @testset "Simple graphs through eight vertices" begin
            # https://oeis.org/A000088, offset 0.
            expected = [1, 1, 2, 4, 11, 34, 156, 1044, 12346]
            T = InducedFlag{Graph,true}
            flags = generateAll(T, 8, binomial(8, 2))
            check_size_counts(flags, expected)
            for n in 0:8
                check_labeled_mass(flags, n, big(2)^binomial(n, 2))
            end
            # The non-induced convention drops isolated vertices. Removing
            # one isolate gives a bijection to graphs on n-1 vertices.
            reduced = generateAll(Graph, 7, binomial(7, 2); parallel=false)
            check_size_counts(reduced, vcat(1, diff(expected[1:8])))
            @test all(F -> !any(FlagSOS.isolatedVertices(F)), reduced)
        end

        @testset "Oriented graphs (no loops or digons)" begin
            # https://oeis.org/A001174, offset 1; prepend the empty object.
            expected = [1, 1, 2, 7, 42, 582]
            T = InducedFlag{DirectedGraph{false},true}
            flags = generateAll(T, 5, binomial(5, 2); parallel=false)
            check_size_counts(flags, expected)
            for n in 0:5
                check_labeled_mass(flags, n, big(3)^binomial(n, 2))
            end
            @test all(!F.F.A[i, i] for F in flags for i in 1:size(F))
            @test all(!(F.F.A[u, v] && F.F.A[v, u]) for F in flags
                      for (u, v) in combinations(1:size(F), 2))
        end

        @testset "3-uniform hypergraphs through six vertices" begin
            # https://oeis.org/A000665, offset 0.
            expected = [1, 1, 1, 2, 5, 34, 2136]
            T = InducedFlag{Hypergraph{3},true}
            flags = generateAll(T, 6, binomial(6, 3))
            check_size_counts(flags, expected)
            @test all(all(==(3), sum(F.F.A; dims=2)) for F in flags)
            for n in 0:6
                check_labeled_mass(flags, n, big(2)^binomial(n, 3))
            end
        end

        @testset "Rooted graphs and both partial-labeling paths" begin
            # https://oeis.org/A000666 counts rooted graphs on n+1 vertices.
            # Only F.n == 1 is rooted; this call also returns unrooted flags.
            unrooted = [1, 1, 2, 4, 11, 34, 156, 1044]
            rooted = [0, 1, 2, 6, 20, 90, 544, 5096]
            T = PartiallyLabeledFlag{InducedFlag{Graph,true}}
            for use_unlabeled in (false, true)
                flags = generateAll(T, 7, [1, 21]; use_unlabeled)
                check_size_counts(flags, unrooted + rooted)
                @test [count(F -> size(F) == n && F.n == 0, flags) for n in 0:7] == unrooted
                roots = filter(F -> F.n == 1, flags)
                @test [count(F -> size(F) == n, roots) for n in 0:7] == rooted
                for n in 1:7
                    check_labeled_mass(roots, n, big(2)^binomial(n, 2); fixed=1)
                end
            end
        end

        @testset "Fixed and interchangeable edge colors" begin
            # 0 means nonedge; 1 and 2 are edge colors. Burnside gives a separate
            # oracle for each interpretation of color names.
            @test [edge_color_count(n) for n in 0:5] == [1, 1, 3, 10, 66, 792]
            for colorblind in (false, true), parallel in (false, true)
                T = InducedFlag{EdgeColoredGraph{2,colorblind},true}
                flags = generateAll(T, 5, 10; parallel)
                check_size_counts(flags, [edge_color_count(n; colorblind) for n in 0:5])
                if !colorblind
                    for n in 0:5
                        check_labeled_mass(flags, n, big(3)^binomial(n, 2))
                    end
                    # A fixed palette must include an edge of either color,
                    # even when no smaller color has appeared in the graph.
                    for c in 1:2
                        @test T(EdgeColoredGraph{2,false}([0 c; c 0])) in flags
                    end
                end
            end
        end

        @testset "Constant-weight codes and triple configurations" begin
            # Weight 3 and distance 4 are precisely partial Steiner triple
            # systems. A system with m triples has at most 3m used points.
            # https://oeis.org/A082789, offset 1; add the empty configuration.
            flags = generateAll(ConstantWeightCode{3,4}, 12, 4)
            @test [count(F -> countEdges(F) == [m], flags) for m in 0:4] == [1, 1, 2, 5, 16]
            @test length(flags) == length(Set(flags)) == 25
            @test all(F -> !any(FlagSOS.isolatedVertices(F)), flags)

            # The maximal systems form an independently tabulated subfamily.
            # https://oeis.org/A006181, n=3,...,10 (maximal, not maximum).
            T = InducedFlag{ConstantWeightCode{3,4},true}
            systems = generateAll(T, 10, binomial(10, 2) ÷ 3)
            @test length(systems) == length(Set(systems))
            @test [count(F -> size(F) == n && maximal_triple_system(F), systems)
                   for n in 3:10] == [1, 1, 1, 2, 2, 4, 10, 47]
            for F in systems
                A = F.F.A
                @test all(==(3), sum(A; dims=2))
                @test all(sum(A[i, :] .& A[j, :]) <= 1
                          for (i, j) in combinations(1:size(A, 1), 2))
            end
        end

        @testset "Binary trees through twelve leaves" begin
            # https://oeis.org/A001190, n=1,...,12. The library also includes
            # one empty tree; its size-zero count is 1, unlike A001190(0)=0.
            expected = [1, 1, 1, 1, 2, 3, 6, 11, 23, 46, 98, 207, 451]
            for T in (BinaryTree, BinaryTreeFlag)
                trees = generateAll(T, 12)
                check_size_counts(trees, expected)
            end
            # Ordered children instead give Catalan(n-1) trees on n leaves.
            ordered = generateAll(BinaryTree, 8; upToIso=false)
            @test length(ordered) == length(Set(ordered))
            @test [count(F -> size(F) == n, ordered) for n in 1:8] ==
                  [binomial(2n - 2, n - 1) ÷ n for n in 1:8]
        end

        @testset "Symmetric monomials by degree" begin
            # https://oeis.org/A000041, n=0,...,12: unrestricted integer partitions.
            expected = [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77]
            monomials = generateAll(SymmetricFunction, 12, 12)
            @test length(monomials) == length(Set(monomials)) == sum(expected)
            @test [count(F -> countEdges(F) == [d], monomials) for d in 0:12] == expected
            # At most 3 nonzero exponents correspond, by partition conjugation,
            # to parts of sizes 1, 2, 3: a + 2b + 3c = d.
            restricted = generateAll(SymmetricFunction, 3, 12)
            @test length(restricted) == length(Set(restricted))
            @test all(F -> size(F) <= 3, restricted)
            @test [count(F -> countEdges(F) == [d], restricted) for d in 0:12] ==
                  [count(a + 2b + 3c == d for a in 0:d, b in 0:(d ÷ 2), c in 0:(d ÷ 3))
                   for d in 0:12]
        end
    finally
        FlagSOS.Memoization.empty_cache!(generateAll)
    end
end
