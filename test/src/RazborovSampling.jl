using FlagSOS, Test, Logging

const IG = InducedFlag{Graph,true}
const Rat = Rational{Int}

quiet(f) = with_logger(NullLogger()) do
    redirect_stdout(f, devnull)
end

function make_inequality(model, level, base)
    k = size(base)
    A = falses(k+1, k+1)
    A[1:k, 1:k] .= base.F.A
    A[1, end] = A[end, 1] = true
    unit = PartiallyLabeledFlag(base, k)
    extension = PartiallyLabeledFlag(IG(Graph(A)), k)
    return quiet(() -> addInequality_Razborov!(model, 3 // 1 * unit - 7 // 1 * extension, level))
end

# Apply the existing quadratic-module multiplication to fixed-type SDP data,
# independently of the new default path through its Razborov base model.
function fixed_quadratic!(q::QuadraticModule{T,U,B,N,D}, reserved=0) where {T<:InducedFlag,U,B,N,D}
    computeSDP!(q.baseModel, reserved + q.reservedVerts; use_downwards=false)
    result = Dict()
    population = N == :limit ? N : N - reserved
    for (G, data) in q.baseModel.sdpData
        product = QuantumFlag{T}(FlagSOS.glueFinite(
            population, G, q.inequality; base_model=q.baseModel.parentModel,
        ))
        if N != :limit
            product = add_verts(
                q.baseModel.parentModel, product, q.baseModel.lvl + FlagSOS.free_verts(q.inequality),
            )
        end
        for (F, coefficient) in labelCanonically(product).coeff
            blocks = get!(result, F, Dict())
            for (mu, block) in data
                blocks[mu] = haskey(blocks, mu) ? blocks[mu] + coefficient * block : coefficient * block
            end
        end
    end
    q.sdpData = result
    return q
end

is_downwards_key(key) = first(key) === :sample_coefficients_downwards

@testset "Razborov downwards sampling" begin
    @testset "Main blocks and forbidden flags" begin
        # N below the outer degree also exercises vanishing overlap weights.
        for N in (3, 20, :limit), restricted in (false, true)
            model = FlagModel{IG,N,Rat}()
            if restricted
                addForbiddenFlag!(model, IG(Graph(Bool[0 1 1; 1 0 1; 1 1 0])))
            end
            block = quiet(() -> addRazborovBlock!(model, 4))
            reference = deepcopy(block)
            quiet(() -> computeSDP!(reference, 0; use_downwards=false))
            quiet(() -> computeSDP!(model))
            @test block.sdpData == reference.sdpData
            @test count(is_downwards_key, keys(model.glue_cache)) == 1
            @test all(is_downwards_key, keys(model.glue_cache))
            @test only(keys(model.glue_cache))[7] == 2

            cached_products = only(values(model.glue_cache))
            quiet(() -> computeSDP!(model))
            @test only(values(model.glue_cache)) === cached_products
        end
    end

    @testset "Retained base labels and inequality modules" begin
        vertex = IG(Graph(falses(1, 1)))
        path = IG(Graph(Bool[0 1 1; 1 0 0; 1 0 0]))
        for N in (20, :limit), (base, level) in ((vertex, 4), (path, 5))
            model = FlagModel{IG,N,Rat}()
            q = make_inequality(model, level, base)
            empty!(model.glue_cache)
            reference = deepcopy(q)
            quiet(() -> fixed_quadratic!(reference))
            quiet(() -> computeSDP!(model))
            @test q.baseModel.sdpData == reference.baseModel.sdpData
            @test q.sdpData == reference.sdpData
            @test all(type(F) == base for F in keys(q.baseModel.sdpData))
            @test count(is_downwards_key, keys(model.glue_cache)) == 1
            key = only(filter(is_downwards_key, collect(keys(model.glue_cache))))
            @test key[4] == base
        end
    end

    @testset "Reserved vertices distinguish cached populations" begin
        model = FlagModel{IG,20,Rat}()
        block = quiet(() -> addRazborovBlock!(model, 4))
        for reserved in (0, 2)
            reference = deepcopy(block)
            empty!(reference.parentModel.glue_cache)
            quiet(() -> computeSDP!(reference, reserved; use_downwards=false))
            quiet(() -> computeSDP!(block, reserved))
            @test block.sdpData == reference.sdpData
        end
        @test Set(key[5] for key in keys(model.glue_cache)) == Set((20, 18))
    end

    @testset "Non-induced models retain their existing path" begin
        model = FlagModel{Graph,20,Rat}()
        block = quiet(() -> addRazborovBlock!(model, 2))
        reference = deepcopy(block)
        quiet(() -> computeSDP!(reference, 0; use_downwards=false))
        quiet(() -> computeSDP!(block, 0))
        @test block.sdpData == reference.sdpData
        @test !any(is_downwards_key, keys(model.glue_cache))
    end
end
