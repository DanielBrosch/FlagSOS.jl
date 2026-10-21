using FlagSOS, Test, LinearAlgebra, Logging

const IG = InducedFlag{Graph,true}
const RF = PartiallyLabeledFlag{IG}
const QQ = Rational{Int}
const edge = IG(Bool[0 1; 1 0])
const e = RF(edge, 1)
const u = RF(IG(falses(1, 1)), 1)
const endpoint = labelCanonically(RF(IG(Bool[0 1 0; 1 0 1; 0 1 0]), 1))
const triangle = IG(Bool[0 1 1; 1 0 1; 1 1 0])

function quiet(f)
    return with_logger(NullLogger()) do
        redirect_stdout(devnull) do
            f()
        end
    end
end

function cycle(n)
    A = falses(n, n)
    for v in 1:n
        w = mod1(v + 1, n)
        A[v, w] = A[w, v] = true
    end
    return A
end

# Independent induced-subset counts, rather than a second use of the sampler.
function density(H, A)
    n = size(A, 1)
    target = labelCanonically(H)
    hits = count(FlagSOS.combinations(1:n, size(H))) do S
        labelCanonically(IG(A[S, S])) == target
    end
    return hits // binomial(n, size(H))
end

function column_value(eq, i, A)
    return sum(get(col, i, 0) * density(H, A) for (H, col) in eq.sdpData; init=0//1)
end

@testset "Finite induced products and equality modules" begin
    @testset "Cache distinguishes actual populations" begin
        fresh = Dict(N => FlagSOS.glueFinite(N, e, e) for N in (:limit, 7, 6))
        @test get(fresh[:limit].coeff, endpoint, 0) == 0
        @test fresh[7].coeff[endpoint] == 1//12
        @test fresh[6].coeff[endpoint] != fresh[7].coeff[endpoint]
        for populations in ((:limit, 7, 6), (7, :limit, 6), (6, 7, :limit))
            m = FlagModel{IG,7,QQ}()
            for N in populations
                @test FlagSOS.glueFinite(N, e, e; base_model=m) == fresh[N]
            end
            entries = length(m.glue_cache)
            for N in reverse(populations)
                @test FlagSOS.glueFinite(N, e, e; base_model=m) == fresh[N]
            end
            @test length(m.glue_cache) == entries == 3
        end
    end

    @testset "Parent context and exact rooted equality coefficients" begin
        for D in (QQ, Rational{BigInt}), reserved in (0, 1)
            n = 7 - reserved
            m = FlagModel{IG,7,D}()
            addForbiddenFlag!(m, triangle)
            eq = quiet(() -> addEquality!(m, D(n - 1)*e - D(2)*u, 100; maxVertices=3))
            @test eq.parentModel === m
            quiet(() -> computeSDP!(eq, reserved))
            @test !isempty(eq.sdpData)
            @test all(size(H) == 3 && FlagSOS.isAllowed(m, H) for H in keys(eq.sdpData))
            # Every vertex in C_n has degree two, so every multiplier of this
            # rooted equality must evaluate to zero. Dropping labels without
            # their averaging factors gave 14/15 for the edge column on C7.
            @test all(iszero(column_value(eq, i, cycle(n))) for i in eachindex(eq.basis))
            edge_column = findfirst(==(e), eq.basis)
            @test edge_column !== nothing
            @test any(!iszero(get(col, edge_column, 0)) for col in values(eq.sdpData))
            @test column_value(eq, edge_column, falses(n, n)) == 0
            nonedge_column = findfirst(==(RF(IG(falses(2, 2)), 1)), eq.basis)
            @test column_value(eq, nonedge_column, falses(n, n)) == -2
            standalone = FlagSOS.EqualityModule{IG,RF,7,D}(eq.equality)
            append!(standalone.basis, eq.basis)
            quiet(() -> computeSDP!(standalone, reserved))
            @test standalone.parentModel === nothing
            @test haskey(standalone.sdpData, labelCanonically(triangle))
            @test eq.sdpData == filter(p -> FlagSOS.isAllowed(m, p.first), standalone.sdpData)
        end

        center = RF(IG(Bool[0 1 1; 1 0 0; 1 0 0]), 1)
        @test FlagSOS.unlabel_fact(center) == 1//3
        @test FlagSOS.unlabel_fact(endpoint) == 2//3

        # e + nonedge = the rooted unit, at finite N and in the limit.
        for N in (7, :limit)
            m = FlagModel{IG,N,QQ}()
            partition = 1//1*e + 1//1*RF(IG(falses(2, 2)), 1) - 1//1*u
            eq = quiet(() -> addEquality!(m, partition, 100; maxVertices=3))
            quiet(() -> computeSDP!(eq))
            @test all(iszero(c) for col in values(eq.sdpData) for c in values(col))
        end

        empty_eq = FlagSOS.EqualityModule{IG,RF,7,QQ}(QuantumFlag{RF,QQ}())
        push!(empty_eq.basis, e)
        @test computeSDP!(empty_eq) === nothing
        @test isempty(empty_eq.sdpData)
        no_basis = FlagSOS.EqualityModule{IG,RF,7,QQ}(1//1*e)
        @test computeSDP!(no_basis) === nothing
    end

    @testset "Unrooted equalities and common order across submodels" begin
        for assembly in (:jump, :standard, :compute)
            m = FlagModel{IG,7,QQ}()
            rooted = quiet(() -> addEquality!(m, 6//1*e - 2//1*u, 100; maxVertices=3))
            unrooted = quiet(() -> addEquality!(m, 1//1*edge - 1//3*one(IG), 100; maxVertices=4))
            @test unrooted.parentModel === m
            # A smaller PSD submodel exercises lifting matrix coefficients as
            # well as the scalar coefficients of the equality multipliers.
            psd = quiet(() -> addRazborovBlock!(m, 2))
            quiet(() -> computeSDP!(rooted))
            quiet(() -> computeSDP!(unrooted))
            quiet(() -> computeSDP!(psd))
            @test all(size(H) == 3 for H in keys(rooted.sdpData))
            @test all(size(H) == 4 for H in keys(unrooted.sdpData))
            @test all(size(H) == 2 for H in keys(psd.sdpData))
            before_psd = deepcopy(psd.sdpData)
            m.objective = -1//1*one(IG)
            m.onlyFeasibility = true
            if assembly == :jump
                built = quiet(() -> buildJuMPModel(m))
                @test all(size(H) == 4 for H in keys(built.variables))
            elseif assembly == :standard
                built = quiet(() -> buildStandardModel(m))
                @test all(size(H) == 4 for H in built.vars)
                @test all(size(H) == 4 for H in keys(built.obj.coeff))
            else
                quiet(() -> computeSDP!(m))
            end
            @test all(size(H) == 4 for sm in m.subModels for H in keys(sm.sdpData))
            for eq in (rooted, unrooted)
                @test all(iszero(column_value(eq, i, cycle(7))) for i in eachindex(eq.basis))
            end
            for mu in keys(modelBlockSizes(psd))
                old = sum(density(H, cycle(7))*blocks[mu] for (H, blocks) in before_psd if haskey(blocks, mu))
                new = sum(density(H, cycle(7))*blocks[mu] for (H, blocks) in psd.sdpData if haskey(blocks, mu))
                @test old == new
            end
            data = deepcopy([sm.sdpData for sm in m.subModels])
            quiet(() -> buildJuMPModel(m))
            quiet(() -> buildStandardModel(m))
            @test [sm.sdpData for sm in m.subModels] == data
        end
    end
end
