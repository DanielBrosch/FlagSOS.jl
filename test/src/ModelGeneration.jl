using FlagSOS, Test, LinearAlgebra

const IG = InducedFlag{Graph,true}
const P = PartiallyLabeledFlag{IG}

function reference_model_generation(T, n, bounds, model; initial_flag=one(T), kwargs...)
    return generateAll(
        T, n, bounds; initial_flag,
        withProperty=F -> FlagSOS.isAllowed(model, F),
        withPropertyMarked=F -> FlagSOS.isAllowed(model, F), kwargs...,
    )
end

@testset "Model-aware partially labeled generation" begin
    @testset "Restrictions, seed labels, and edge bounds" begin
        model = FlagModel{IG,49,Rational{Int}}()
        addForbiddenFlag!(model, IG(Graph(.!Matrix{Bool}(I, 3, 3))))
        addForbiddenFlag!(model, IG(Graph(falses(4, 4))))
        edge = IG(Graph(Bool[0 1; 1 0]))
        path = IG(Graph(Bool[0 1 0; 1 0 1; 0 1 0]))
        for seed in (one(P), P(edge, 2), P(edge, 1), P(path, 1)),
            labels in seed.n:(seed.n + 1), edges in (0, 2, 100)
            expected = reference_model_generation(P, 4, [labels, edges], model; initial_flag=seed)
            actual = FlagSOS._generate_model_flags(P, 4, [labels, edges], model; initial_flag=seed)
            @test actual == expected
            @test first(actual) == seed
        end

        # Forbidden seeds and requests smaller than the seed still return it.
        seed = P(IG(Graph(.!Matrix{Bool}(I, 3, 3))), 3)
        for n in (2, 4)
            @test FlagSOS._generate_model_flags(P, n, [3, 100], model; initial_flag=seed) ==
                  reference_model_generation(P, n, [3, 100], model; initial_flag=seed)
        end

        # Nonhomogeneous forbidden graphs use the general isomorphism matcher;
        # larger sets share subset traversal as in the original implementation.
        for forbidden in ([path], filter(F -> size(F) == 4, generateAll(IG, 4, 100)))
            empty!(model.forbiddenFlags)
            foreach(F -> addForbiddenFlag!(model, F), forbidden)
            # The reference closures capture the mutable model, so explicitly
            # discard their old cache entries after changing its restrictions.
            FlagSOS.Memoization.empty_cache!(generateAll)
            @test FlagSOS._generate_model_flags(P, 4, [2, 100], model) ==
                  reference_model_generation(P, 4, [2, 100], model)
        end
    end

    @testset "Four-label Ramsey types on seven vertices" begin
        model = FlagModel{IG,49,Rational{Int}}()
        addForbiddenFlag!(model, IG(Graph(.!Matrix{Bool}(I, 5, 5))))
        addForbiddenFlag!(model, IG(Graph(falses(5, 5))))
        path = IG(Graph(Bool[0 1 0 0; 1 0 1 0; 0 1 0 1; 0 0 1 0]))
        seed = P(path, 4)
        expected = reference_model_generation(P, 7, [4, 10000], model; initial_flag=seed)
        actual = FlagSOS._generate_model_flags(P, 7, [4, 10000], model; initial_flag=seed)
        @test actual == expected
        @test length(actual) == 6169
        @test all(F.n == 4 && type(F) == path for F in actual)
        @test FlagSOS._generate_model_flags(
            P, 7, [4, 10000], model; initial_flag=seed, parallel=false,
        ) == actual

        # Exercise both coefficient callers on the same nontrivial base, with
        # the old generation path supplying independent reference flag vectors.
        for balanced in (false, true)
            n = balanced ? 6 : 7
            @test FlagSOS.sample_coefficients(
                IG, n, path; n_outer=7, base_model=model, N=49, only_balanced=balanced,
            ) == FlagSOS.sample_coefficients(
                IG, n, path; n_outer=7, base_model=model, N=49, only_balanced=balanced,
                all_flags=expected,
            )
        end
        @test FlagSOS.sample_coefficients_downwards(
            IG, 6, path; n_outer=7, base_model=model, N=49, max_type_size=4,
        ) == FlagSOS.sample_coefficients_downwards(
            IG, 6, path; n_outer=7, base_model=model, N=49, max_type_size=4,
            all_flags=expected,
        )
    end

    @testset "Cache keys snapshot the forbidden set" begin
        FlagSOS.Memoization.empty_cache!(generateAll)
        model = FlagModel{IG}()
        first_result = FlagSOS._generate_model_flags(P, 4, [2, 100], model)
        @test FlagSOS._generate_model_flags(P, 4, [2, 100], model) === first_result
        @test FlagSOS._generate_model_flags(P, 4, [2, 100], deepcopy(model)) === first_result

        addForbiddenFlag!(model, IG(Graph(.!Matrix{Bool}(I, 3, 3))))
        restricted = FlagSOS._generate_model_flags(P, 4, [2, 100], model)
        @test restricted !== first_result
        @test length(restricted) < length(first_result)
        @test restricted == reference_model_generation(P, 4, [2, 100], model)
        @test FlagSOS._generate_model_flags(P, 4, [2, 100], deepcopy(model)) === restricted
        empty!(model.forbiddenFlags)
        @test FlagSOS._generate_model_flags(P, 4, [2, 100], model) === first_result
    end

    @testset "Other algebras and unsupported model restrictions" begin
        C = InducedFlag{ConstantWeightCode{3,4},true}
        PC = PartiallyLabeledFlag{C}
        model = FlagModel{C}()
        addForbiddenFlag!(model, C(ConstantWeightCode{3,4}(Bool[1 1 1])))
        @test FlagSOS._generate_model_flags(PC, 4, [2, 2], model) ==
              reference_model_generation(PC, 4, [2, 2], model)

        PG = PartiallyLabeledFlag{Graph}
        model = FlagModel{Graph}()
        addForbiddenFlag!(model, Graph(Bool[0 1; 1 0]))
        @test FlagSOS._generate_model_flags(PG, 4, [2, 100], model) ==
              reference_model_generation(PG, 4, [2, 100], model)
    end
end
