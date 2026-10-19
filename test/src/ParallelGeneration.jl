using FlagSOS, Test

Base.include(FlagSOS, joinpath(@__DIR__, "..", "reference_generation.jl"))

@testset "Parallel generation" begin
    IG = InducedFlag{Graph,true}
    P = PartiallyLabeledFlag{IG}
    edge = IG(Graph(Bool[0 1; 1 0]))
    path = IG(Graph(Bool[0 1 1; 1 0 0; 1 0 0]))
    cases = [
        (IG, 6, [100], one(IG)),
        (Graph, 5, [4], one(Graph)),
        (P, 5, [3, 100], one(P)),
        (P, 5, [2, 3], P(edge, 1)),
        (P, 5, [3, 100], P(path, 3)),
        (P, 5, [2, 100], P(IG(Graph(falses(2, 2))), 1)),
    ]
    C = InducedFlag{ConstantWeightCode{3,4},true}
    PC = PartiallyLabeledFlag{C}
    push!(cases, (PC, 5, [3, 2], one(PC)))
    for (T, n, bounds, seed) in cases
        expected = Set(FlagSOS._generation_reference(T, n, bounds; initial_flag=seed))
        for use_unlabeled in (false, true), parallel in (false, true)
            actual = generateAll(T, n, bounds; initial_flag=seed, use_unlabeled, parallel)
            @test Set(actual) == expected
            @test length(actual) == length(expected)
            @test first(actual) == seed
        end
    end

    property = F -> F.n <= 1 || !F.F.F.A[1, 2]
    marked = F -> F.F.n <= 2
    expected = Set(FlagSOS._generation_reference(
        P, 5, [3, 100]; withProperty=property, withPropertyMarked=marked
    ))
    @test Set(generateAll(P, 5, [3, 100]; withProperty=property, withPropertyMarked=marked)) == expected

    # Exercise enough states and independent labeling jobs to fill 128 workers.
    serial = generateAll(P, 6, [2, 100]; parallel=false)
    expected = Set(serial)
    for _ in 1:3
        FlagSOS.Memoization.empty_cache!(generateAll)
        actual = generateAll(P, 6, [2, 100])
        @test Set(actual) == expected
        @test actual == serial
        @test issorted(size.(actual))
    end

    # Worker exceptions must propagate instead of leaving Channel consumers
    # blocked forever. Also exercise tasks called from an existing worker task.
    fail = F -> size(F) >= 5 ? error("generation callback failed") : true
    @test_throws Exception generateAll(IG, 5, [100]; withProperty=fail)
    worker_error = Threads.nthreads() == 1 ? ErrorException : CompositeException
    @test_throws worker_error generateAll(IG, 5, [100]; withPropertyMarked=fail)
    result = fetch(Threads.@spawn generateAll(P, 5, [3, 100]; parallel=true))
    @test Set(result) == Set(generateAll(P, 5, [3, 100]; parallel=false))
end
