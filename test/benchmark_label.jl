# Run with: julia --project=. --startup-file=no test/benchmark_label.jl
# Run the same script on each revision; timings exclude compilation.
using FlagSOS, Random, LinearAlgebra, Printf

function benchmark_label(name, F; repetitions=100)
    FlagSOS.label(F; removeIsolated=false)
    GC.gc()
    samples = [@timed FlagSOS.label(F; removeIsolated=false) for _ in 1:repetitions]
    @printf("%-20s %9.2f μs  %10d bytes  |Aut|=%d\n",
            name, minimum(s.time for s in samples) * 1e6,
            minimum(s.bytes for s in samples), FlagSOS.order(samples[1].value[3]))
end

rng = MersenneTwister(283)
for n in (12, 24)
    A = falses(n, n)
    for i in 1:n, j in (i + 1):n
        A[i, j] = A[j, i] = rand(rng, Bool)
    end
    benchmark_label("Random graph, n=$n", Graph(A))
end
for n in (12, 24)
    A = falses(n, n)
    for i in 1:n
        j = mod1(i + 1, n)
        A[i, j] = A[j, i] = true
    end
    benchmark_label("Cycle, n=$n", Graph(A))
end
benchmark_label("Complete graph, n=12", Graph(.!Matrix{Bool}(I, 12, 12)); repetitions=20)
fano = falses(7, 7)
for (i, e) in enumerate(((1, 2, 3), (1, 4, 5), (1, 6, 7), (2, 4, 6),
                         (2, 5, 7), (3, 4, 7), (3, 5, 6)))
    fano[i, collect(e)] .= true
end
benchmark_label("Fano code", ConstantWeightCode{3,4}(fano))
cycle = Graph(Bool[0 1 0 0 0 1; 1 0 1 0 0 0; 0 1 0 1 0 0;
                   0 0 1 0 1 0; 0 0 0 1 0 1; 1 0 0 0 1 0])
benchmark_label("Labeled cycle", PartiallyLabeledFlag(cycle, 2))
