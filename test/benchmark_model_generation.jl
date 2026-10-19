# Run without competing benchmark jobs, e.g.:
# julia --project=. --threads=8 test/benchmark_model_generation.jl
using FlagSOS, LinearAlgebra, Printf

const IG = InducedFlag{Graph,true}
const P = PartiallyLabeledFlag{IG}
const base = IG(Graph(Bool[0 1 0 0; 1 0 1 0; 0 1 0 1; 0 0 1 0]))
const seed = P(base, 4)
const model = FlagModel{IG,49,Rational{Int}}()
addForbiddenFlag!(model, IG(Graph(.!Matrix{Bool}(I, 5, 5))))
addForbiddenFlag!(model, IG(Graph(falses(5, 5))))

allowed = F -> FlagSOS.isAllowed(model, F)
legacy_flags() = generateAll(
    P, 7, [4, 10000]; initial_flag=seed,
    withProperty=allowed, withPropertyMarked=allowed,
)
model_flags() = FlagSOS._generate_model_flags(P, 7, [4, 10000], model; initial_flag=seed)
legacy_coefficients() = FlagSOS.sample_coefficients(
    IG, 7, base; N=49, only_balanced=false, base_model=model, all_flags=legacy_flags(),
)
model_coefficients() = FlagSOS.sample_coefficients(
    IG, 7, base; N=49, only_balanced=false, base_model=model,
)

function benchmark_model_call(name, f, expected; trials=3)
    # Warm compilation and isomorphism checks, but clear the generation cache
    # before each measurement. Equality includes canonical flags and ordering.
    @assert f() == expected
    times, bytes, gc_times = Float64[], Int[], Float64[]
    for _ in 1:trials
        FlagSOS.Memoization.empty_cache!(generateAll)
        GC.gc()
        run = @timed f()
        @assert run.value == expected
        push!(times, run.time)
        push!(bytes, run.bytes)
        push!(gc_times, run.gctime)
    end
    @printf(
        "%s,%d,%.6f,%d,%.6f\n", name, Threads.nthreads(),
        minimum(times), minimum(bytes), minimum(gc_times),
    )
    flush(stdout)
end

expected_flags = legacy_flags()
@assert model_flags() == expected_flags
expected_coefficients = legacy_coefficients()
@assert model_coefficients() == expected_coefficients
println("case,threads,seconds,bytes,gc_seconds")
benchmark_model_call("generation_incremental", legacy_flags, expected_flags)
benchmark_model_call("generation_model", model_flags, expected_flags)
benchmark_model_call("coefficients_incremental", legacy_coefficients, expected_coefficients)
benchmark_model_call("coefficients_model", model_coefficients, expected_coefficients)
