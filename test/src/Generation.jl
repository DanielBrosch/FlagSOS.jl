using FlagSOS, Test

const IG = InducedFlag{Graph,true}

function compare_generation(T, n, limits; initial_flag=one(T), kwargs...)
    actual = generateAll(T, n, limits; initial_flag=initial_flag, kwargs...)
    expected = generateAll(
        T, n, limits; initial_flag=initial_flag, use_unlabeled=false, kwargs...
    )
    @test Set(actual) == Set(expected)
    @test length(actual) == length(Set(actual))
    @test first(actual) == initial_flag
    return actual
end

@testset "Unlabeled-first generation" begin
    @testset "Graphs and nontrivial seeds" begin
        edge = Graph(Bool[0 1; 1 0])
        path = Graph(Bool[0 1 0; 1 0 1; 0 1 0])
        for T in (Graph, IG)
            wrap(g) = T == Graph ? g : T(g)
            P = PartiallyLabeledFlag{T}
            seeds = [
                one(P),
                P(wrap(Graph(falses(1, 1))), 1),
                P(wrap(edge), 2),
                P(wrap(edge), 1),
                P(wrap(path), 2),
                P(wrap(Graph(falses(2, 2))), 1),
            ]
            for seed in seeds, n in max(1, size(seed)):4,
                k in seed.n:min(n, seed.n + 2), e in (0, 2, 100)
                compare_generation(P, n, [k, e]; initial_flag=seed)
            end
            # The seed is returned as supplied, even when it is noncanonical,
            # violates the bounds, or is larger than the requested size.
            seed = P(wrap(path), 1)
            @test generateAll(P, 2, [0, 0]; initial_flag=seed) == [seed]
            compare_generation(P, 5, [3, 100]; initial_flag=seed)
        end
    end

    @testset "Independent exhaustive graph counts" begin
        P = PartiallyLabeledFlag{IG}
        expected = Set{P}()
        # Every adjacency matrix, with every possible number of fixed labels.
        for n in 0:4
            edges = [(u, v) for u in 1:n for v in (u + 1):n]
            for mask in 0:(2^length(edges) - 1)
                A = falses(n, n)
                for (j, (u, v)) in enumerate(edges)
                    A[u, v] = A[v, u] = !iszero(mask & (1 << (j - 1)))
                end
                for k in 0:n
                    push!(expected, labelCanonically(P(IG(Graph(A)), k)))
                end
            end
        end
        actual = generateAll(P, 4, [4, 100])
        @test Set(actual) == expected
        @test issorted(size.(actual))
        @test count(F -> size(F) == 4 && F.n == 4, actual) == 64
    end

    @testset "Unlabeled seed vertices cannot become new labels" begin
        P = PartiallyLabeledFlag{IG}
        seed = P(IG(Graph(Bool[0 1; 1 0])), 1)
        flags = generateAll(P, 3, [2, 100]; initial_flag=seed)
        forbidden = P(IG(Graph(Bool[0 1 0; 1 0 0; 0 0 0])), 2)
        allowed = P(IG(Graph(Bool[0 0 1; 0 0 0; 1 0 0])), 2)
        @test forbidden ∉ flags
        @test allowed ∈ flags
    end

    @testset "Constant-weight codes" begin
        C = ConstantWeightCode{3,4}
        for T in (C, InducedFlag{C,true}, InducedFlag{C,false})
            wrap(g) = T == C ? g : T(g)
            P = PartiallyLabeledFlag{T}
            for k in 0:3, e in (0, 1, 2)
                compare_generation(P, 4, [k, e])
            end
            edge = wrap(C(Bool[1 1 1]))
            isolated = wrap(C(falses(0, 3)))
            for seed in (P(edge, 1), P(edge, 3), P(isolated, 3)), k in seed.n:3
                compare_generation(P, 5, [k, 2]; initial_flag=seed)
            end
        end
    end

    @testset "Callbacks and unsupported wrappers keep incremental semantics" begin
        P = PartiallyLabeledFlag{IG}
        property = F -> F.n <= 1 || !F.F.F.A[1, 2]
        marked = F -> F.F.n <= 1
        compare_generation(P, 4, [3, 100]; withProperty=property)
        compare_generation(P, 4, [3, 100]; withPropertyMarked=marked)
        compare_generation(P, 4, [3, 100]; withProperty=property, withPropertyMarked=marked)
        nested = PartiallyLabeledFlag{P}
        compare_generation(nested, 3, [1, 1, 100])
        compare_generation(IG, 3, 2) # integer bound and keyword forwarding
        compare_generation(IG, 4, [2])
    end
end
