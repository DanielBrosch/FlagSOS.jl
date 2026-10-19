# Run with: julia --project=. test/benchmark_generation.jl
using FlagSOS, Printf

function benchmark_generation(name, T, n, limits; initial_flag=one(T))
    results = Any[]
    # The first pair compiles both paths; the second pair measures them.
    # Clear generateAll's cache before EVERY call, including underlying flags.
    for enabled in (false, true, false, true)
        FlagSOS.Memoization.empty_cache!(generateAll)
        GC.gc()
        push!(results, @timed generateAll(
            T, n, limits; initial_flag=initial_flag, use_unlabeled=enabled
        ))
    end
    old, new = results[3:4]
    @assert Set(old.value) == Set(new.value)
    @printf(
        "\n%s: %d flags; original %.3fs / %.1f MB; unlabeled %.3fs / %.1f MB; %.2fx\n",
        name, length(new.value), old.time, old.bytes / 1e6,
        new.time, new.bytes / 1e6, old.time / new.time,
    )
end

const IG = InducedFlag{Graph,true}
const PG = PartiallyLabeledFlag{IG}
benchmark_generation("Graphs, n=7, at most 2 labels", PG, 7, [2, 100])
path = IG(Graph(Bool[0 1 1; 1 0 0; 1 0 0]))
benchmark_generation(
    "Path seed, n=7, 3 labels", PG, 7, [3, 100]; initial_flag=PG(path, 3)
)
const IC = InducedFlag{ConstantWeightCode{3,4},true}
benchmark_generation(
    "Weight-3 codes, n=6, at most 3 labels", PartiallyLabeledFlag{IC}, 6, [3, 100]
)
# A small restrictive seed also records the crossover where relabeling can cost
# more than the original generation. The old path remains explicitly available.
benchmark_generation(
    "Partially labeled path seed, n=5", PG, 5, [3, 100]; initial_flag=PG(path, 1)
)
