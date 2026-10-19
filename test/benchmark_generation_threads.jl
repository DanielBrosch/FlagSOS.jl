# Run separate processes, without competing benchmark jobs, for example:
# julia --project=. --threads=1 test/benchmark_generation_threads.jl 8
# julia --project=. --threads=8 test/benchmark_generation_threads.jl 8
# julia --project=. --threads=128 test/benchmark_generation_threads.jl 8
using FlagSOS, Printf

function benchmark_threaded_generation(name, T, n, bounds; initial_flag=one(T), trials=3)
    FlagSOS.Memoization.empty_cache!(generateAll)
    expected = Set(generateAll(T, n, bounds; initial_flag, parallel=false))
    # Warm the threaded specializations before measuring, including partial
    # labeling and nonempty seed matching. Every timed call starts uncached.
    generateAll(T, n, bounds; initial_flag, parallel=true)
    elapsed = Float64[]
    allocated = Int[]
    gc_elapsed = Float64[]
    for _ in 1:trials
        FlagSOS.Memoization.empty_cache!(generateAll)
        GC.gc()
        run = @timed generateAll(T, n, bounds; initial_flag, parallel=true)
        @assert Set(run.value) == expected
        push!(elapsed, run.time)
        push!(allocated, run.bytes)
        push!(gc_elapsed, run.gctime)
    end
    @printf(
        "%s,%d,%d,%d,%.6f,%d,%.6f\n", name, n, Threads.nthreads(), length(expected),
        minimum(elapsed), minimum(allocated), minimum(gc_elapsed),
    )
end

n = isempty(ARGS) ? 7 : parse(Int, ARGS[1])
const IG = InducedFlag{Graph,true}
const P = PartiallyLabeledFlag{IG}
println("case,vertices,threads,flags,seconds,bytes,gc_seconds")
benchmark_threaded_generation("graphs", IG, n, [100])
benchmark_threaded_generation("partial_graphs", P, n, [2, 100])
path = IG(Graph(Bool[0 1 1; 1 0 0; 1 0 0]))
benchmark_threaded_generation("path_seed", P, n, [3, 100]; initial_flag=P(path, 3))
