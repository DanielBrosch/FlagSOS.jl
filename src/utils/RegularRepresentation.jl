using SparseArrays

function randElement(P::Matrix{Int})
    n = maximum(P)
    cs = randn(n)
    A = [cs[i] for i in P]
    return A
end

function checkAlgebra(P::Matrix{Int})
    A, B = randElement(P), randElement(P)
    C = A * B
    # for i = 1:maximum(P)
    for i in unique(P)
        cs = unique(C[P.==i])
        cs = unique(round.(cs, digits=4))
        if length(cs) > 1
            display(C)
            return false
        end
    end
    return true
end

function tr3(A, B, C)
    n = size(A, 1)
    res = zero(Int)
    for i = 1:n, j = 1:n, k = 1:n
        res += A[i, j] * B[j, k] * C[k, i]
    end
    return res
end

function regularRepresentation(P::Matrix{Int})

    # n = maximum(P)

    inds = sort!(unique(P))
    s = length(inds)

    @assert checkAlgebra(P) "The partition given by the entries of P have to correspond to a Matrix-*-Algebra!"


    As = Dict(i => sparse(Int.(P .== i)) for i in inds)
    # println("new)")

    factors = Dict(i => 1 / sqrt(dot(As[i], As[i])) for i in inds)

    Fs = Dict(i => sparse(float.(As[i])) for i in inds)
    FsTrans = Dict(i => Fs[i]' for i in inds)

    tInd = Dict()
    for i in inds
        for j in inds
            if Fs[i] == FsTrans[j]
                tInd[i] = j
                break
            end
        end
    end
    tIndUnique = deepcopy(tInd)
    for i in inds
        if haskey(tIndUnique, i) && haskey(tIndUnique, tIndUnique[i]) && tIndUnique[i] != i
            delete!(tIndUnique, tIndUnique[i])
        end
    end
    # println(tIndUnique)
    # As(i) = Int.(P .== i)
    # factors = Dict(i => 1 / sqrt(dot(As(i), As(i))) for i = 1:n)

    reg = Dict(k => zeros(Float64, s, s) for k in inds)

    BiBj = zeros(size(P)) #zeros(Int, size(P))

    if (false)
        for (i, a) in enumerate(inds)
            for (j, b) in enumerate(inds)
                # for i = 1:n
                # for j = 1:n
                # @show (i,j, n)
                # BiBj = As(i) * As(j)'
                # BiBj .= As[a] * As[b]'
                BiBj .= Fs[a] * FsTrans[b]
                # @show (i,j, n)
                for k in inds
                    # for k = 1:n
                    # reg[k][i, j] = factors[i] * factors[j] * factors[k] * tr3(As[i], As[j]', As[k]')
                    # reg[k][i, j] = factors[i] * factors[j] * factors[k] * dot(BiBj, As[k]')
                    reg[k][i, j] = factors[a] * factors[b] * dot(BiBj, FsTrans[k])
                end
            end
        end
        # for i = 1:n
        #     for j = 1:n
        #         @show (i,j, n)
        #         # BiBj = As(i) * As(j)'
        #         BiBj .= Fs[i] *FsTrans[j]
        #         @show (i,j, n)
        #         for k = 1:n
        #             # reg[k][i, j] = factors[i] * factors[j] * factors[k] * tr3(As[i], As[j]', As[k]')
        #             reg[k][i, j] = dot(BiBj, FsTrans[k])#* factors[i] * factors[j] * factors[k]
        #             # reg[k][i, j] = factors[i] * factors[j] * factors[k] * dot(BiBj, As(k)')
        #         end
        #     end
        # end
    end

    if (true)
        RegFactors = Dict()
        for i in inds
            for j in inds
                BiBj .= Fs[i] * FsTrans[j]
                for (k, _) in tIndUnique
                    # RegFactors[k, i, j] = dot(BiBj, FsTrans[k]) = tr(kij*)
                    if haskey(RegFactors, (k, i, j))
                        continue
                    end
                    tmp = dot(BiBj, FsTrans[k])
                    # @show (k,i,j)
                    RegFactors[k, i, j] = tmp # = tr(kij*)
                    RegFactors[tInd[j], k, tInd[i]] = tmp # = tr(j*ki)
                    RegFactors[i, tInd[j], tInd[k]] = tmp # = tr(ij*k)
                    RegFactors[j, tInd[i], k] = tmp # = tr(ji*k*)
                    RegFactors[tInd[k], j, i] = tmp # = tr(k*ji*)
                    RegFactors[tInd[i], tInd[k], tInd[j]] = tmp # = tr(i*k*j)
                end
            end
        end

        for (i, a) in enumerate(inds)
            for (j, b) in enumerate(inds)
                for k in inds
                    reg[k][i, j] = factors[a] * factors[b] * RegFactors[k, a, b]
                end
            end
        end
    end
    reg
end