using FlagSOS, Test
using FlagSOS: combinations, subFlag, isAllowed

const IG = InducedFlag{Graph,true}
const PF = PartiallyLabeledFlag{IG}

# Reference formula from the original fixed-type sampler. Keep the overlap
# counting factors separate from the union-count formula used in production.
function reference_sample(n, type; n_outer=n, N=:limit, only_balanced=true,
                          base_model=nothing, all_flags=nothing)
    k = size(type)
    if all_flags === nothing
        all_flags = generateAll(
            PF, n_outer, [k, 10000]; initial_flag=PF(type, k),
            withProperty=F -> isAllowed(base_model, F),
            withPropertyMarked=F -> isAllowed(base_model, F),
        )
    end
    indices = only_balanced ? filter(F -> size(F) == k + div(n-k, 2), all_flags) : all_flags
    outer_flags = filter(F -> size(F) == n_outer, all_flags)
    res = Dict{Tuple{PF,PF},QuantumFlag{PF,Rational{Int}}}()
    for G in outer_flags, a in 0:(n-k)
        only_balanced && 2a != n-k && continue
        m = size(G) - k
        for S1 in combinations((k+1):size(G), a)
            F1 = labelCanonically(subFlag(G, vcat(1:k, S1)))
            other = N == :limit ? setdiff((k+1):size(G), S1) : ((k+1):size(G))
            for b in 0:(n-k-a)
                only_balanced && b != a && continue
                for S2 in combinations(other, b)
                    F2 = labelCanonically(subFlag(G, vcat(1:k, S2)))
                    ov = length(intersect(S1, S2))
                    fact = 1 // (binomial(m, ov) * binomial(m-ov, a-ov) * binomial(m-a, b-ov))
                    probability = N == :limit ? 1 // 1 :
                        (binomial(N-k, ov) * binomial(N-k-ov, a-ov) * binomial(N-k-a, b-ov)) //
                        (binomial(N-k, a) * binomial(N-k, b))
                    product = get!(res, (F1, F2)) do
                        QuantumFlag{PF,Rational{Int}}()
                    end
                    product.coeff[G] = get(product.coeff, G, 0 // 1) + fact * probability
                end
            end
        end
    end
    return indices, outer_flags, res
end

function reference_downwards(n, base; n_outer=n, N=:limit, only_balanced=true,
                             labeled_type=nothing, base_model=nothing)
    k = size(base)
    types = if labeled_type === nothing
        extensions = generateAll(
            PF, n, [k, 10000]; initial_flag=PF(base, k),
            withProperty=F -> isAllowed(base_model, F),
            withPropertyMarked=F -> isAllowed(base_model, F),
        )
        unique(IG[
            iszero(k) ? labelCanonically(F.F) : F.F for F in extensions
            if !only_balanced || iseven(n-size(F))
        ])
    else
        [labeled_type]
    end
    res = Dict{Tuple{PF,PF},QuantumFlag{PF,Rational{Int}}}()
    for type in types
        products = reference_sample(
            n, type; n_outer=n_outer, N=N, only_balanced=only_balanced, base_model=base_model,
        )[3]
        for (pair, product) in products
            res[pair] = labelCanonically(sum(
                c * unlabel(PartiallyLabeledFlag(PF(H.F, k), H.n))
                for (H, c) in product.coeff;
                init=zero(product),
            ))
        end
    end
    return res
end

function check_downwards(n, base; kwargs...)
    indices, outer_flags, actual = FlagSOS.sample_coefficients_downwards(IG, n, base; kwargs...)
    expected = reference_downwards(n, base; kwargs...)
    @test Set(keys(actual)) == Set(keys(expected))
    @test Set(indices) == Set(F for pair in keys(actual) for F in pair)
    @test all(F.n == size(base) && type(F) == base for F in outer_flags)
    for pair in intersect(Set(keys(actual)), Set(keys(expected)))
        @test labelCanonically(actual[pair]) == expected[pair]
        @test all(F == labelCanonically(F) for F in pair)
        @test all(F.n == size(base) && type(F) == base for F in keys(actual[pair].coeff))
    end
end

@testset "Coefficient sampling" begin
    empty_type = one(IG)
    vertex = IG(Graph(falses(1, 1)))
    edge = IG(Graph(Bool[0 1; 1 0]))
    path = IG(Graph(Bool[0 1 1; 1 0 0; 1 0 0]))

    @testset "Fixed-type API" begin
        for (n, outer, base, balanced) in (
            (0, 0, empty_type, true),
            (4, 4, empty_type, true),
            (4, 5, empty_type, true),
            (5, 5, path, true),
            (3, 4, vertex, true),
            (3, 3, empty_type, false),
            (4, 4, edge, false),
        ), N in (:limit, 20)
            actual = FlagSOS.sample_coefficients(IG, n, base; n_outer=outer, N=N, only_balanced=balanced)
            expected = reference_sample(n, base; n_outer=outer, N=N, only_balanced=balanced)
            @test actual == expected
        end
    end

    @testset "All extension types" begin
        for (n, outer, base) in (
            (0, 0, empty_type),
            (4, 4, empty_type),
            (4, 5, edge),
            (5, 5, path),
            (4, 4, vertex),
        ), N in (:limit, 20)
            check_downwards(n, base; n_outer=outer, N=N)
        end
        for N in (4, 5)
            check_downwards(5, path; N=N)
        end
        for base in (empty_type, vertex), N in (:limit, 7)
            check_downwards(3, base; N=N, only_balanced=false)
        end
    end

    @testset "Requested extension labels" begin
        check_downwards(5, empty_type; labeled_type=path, N=20)
        canonical = labelCanonically(PF(IG(Graph(Bool[0 1 0; 1 0 0; 0 0 0])), 1)).F
        requested = permute(canonical, [1, 3, 2])
        @test requested != canonical
        for N in (:limit, 20)
            check_downwards(5, vertex; labeled_type=requested, N=N)
        end
        check_downwards(4, vertex; labeled_type=requested, N=20, only_balanced=false)
        @test_throws AssertionError FlagSOS.sample_coefficients_downwards(IG, 4, edge; labeled_type=vertex)
    end

    @testset "Supplied flags and model restrictions" begin
        flags = generateAll(PF, 4, [0, 10000]; initial_flag=PF(empty_type, 0))
        edgeless = filter(F -> !any(F.F.F.A), flags)
        @test FlagSOS.sample_coefficients(IG, 4, empty_type; all_flags=edgeless, N=20) ==
              reference_sample(4, empty_type; all_flags=edgeless, N=20)
        _, outer, products = FlagSOS.sample_coefficients_downwards(IG, 4; all_flags=edgeless, N=20)
        @test all(F in edgeless for F in outer)
        @test all(F in edgeless for product in values(products) for F in keys(product.coeff))
        @test isempty(FlagSOS.sample_coefficients_downwards(IG, 4; all_flags=PF[])[3])

        model = FlagModel{IG}()
        triangle = IG(Graph(Bool[0 1 1; 1 0 1; 1 1 0]))
        push!(model.forbiddenFlags, labelCanonically(triangle))
        @test FlagSOS.sample_coefficients(IG, 4, empty_type; base_model=model, N=20) ==
              reference_sample(4, empty_type; base_model=model, N=20)
        check_downwards(4, empty_type; base_model=model, N=20)

        F = labelCanonically(PF(edge, 0))
        @test FlagSOS.glueFinite(20, F, F; base_model=model) ==
              reference_sample(4, empty_type; base_model=model, N=20)[3][(F, F)]
    end
end
