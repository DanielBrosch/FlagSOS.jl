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


    As = Dict(i => sparse(Int.(P .== i)) for i = 1:maximum(P))
    println("new)")
    
    factors = Dict(i => 1 / sqrt(dot(As[i], As[i])) for i = 1:n)

    Fs = Dict(i => sparse(float.(As[i]))*factors[i] for i = 1:maximum(P))
    FsTrans = Dict(i => Fs[i]' for i = 1:maximum(P))

    TransposeNumbers = Dict() 
    for i=1:n
        for j=1:n 
            if Fs[i]==FsTrans[j]
                TransposeNumbers[i]=j
                break
            end
        end
    end 
    TransposeNumbersUnique=deepcopy(TransposeNumbers)
    for i=1:n
        if haskey(TransposeNumbersUnique,i)&&  haskey(TransposeNumbersUnique,TransposeNumbersUnique[i]) && TransposeNumbersUnique[i]!=i 
                delete!(TransposeNumbersUnique,TransposeNumbersUnique[i])
        end
    end
    println(TransposeNumbersUnique)
    # As(i) = Int.(P .== i)
    # factors = Dict(i => 1 / sqrt(dot(As(i), As(i))) for i = 1:n)

    reg = Dict(k => zeros(Float64, s, s) for k in inds)

    BiBj =zeros(size(P)) #zeros(Int, size(P))

    if (false) 
        for i = 1:n
            for j = 1:n
                @show (i,j, n)
                # BiBj = As(i) * As(j)'
                BiBj .= Fs[i] *FsTrans[j]
                @show (i,j, n)
                for k = 1:n
                    # reg[k][i, j] = factors[i] * factors[j] * factors[k] * tr3(As[i], As[j]', As[k]')
                    reg[k][i, j] = dot(BiBj, FsTrans[k])#* factors[i] * factors[j] * factors[k]
                    # reg[k][i, j] = factors[i] * factors[j] * factors[k] * dot(BiBj, As(k)')
                end
            end
        end
    end

    if (true) 
        RegFactors = Dict() 
        println(TransposeNumbersUnique.keys)
        for (i,val) in TransposeNumbersUnique
            @show(i,n)
            for (j,val2) in TransposeNumbersUnique
                BiBj .= Fs[i] *FsTrans[j]
                for k=1:n
                    RegFactors[k,i,j] = dot(BiBj, FsTrans[k])
                end
            end
        end

        for i = 1:n
            for j = 1:n
                for k = 1:n
                    used=false 
                    if haskey(RegFactors,(k,i,j))
                        reg[k][i, j] =RegFactors[k,i,j];
                        used=true 
                    elseif haskey(RegFactors,(TransposeNumbers[j],TransposeNumbers[k],i))
                        reg[k][i, j] =RegFactors[TransposeNumbers[j],TransposeNumbers[k],i];
                        used=true
                    elseif haskey(RegFactors,(TransposeNumbers[i],j,TransposeNumbers[k]))
                        reg[k][i, j] =RegFactors[TransposeNumbers[i],j,TransposeNumbers[k]];
                        used=true 
                    elseif haskey(RegFactors,(TransposeNumbers[k],TransposeNumbers[j],TransposeNumbers[i]))
                        reg[k][i, j] =RegFactors[TransposeNumbers[k],TransposeNumbers[j],TransposeNumbers[i]];
                        used=true
                    elseif haskey(RegFactors,(j,TransposeNumbers[i],k))
                        reg[k][i, j] =RegFactors[j,TransposeNumbers[i],k];
                        used=true
                    elseif haskey(RegFactors,(i,k,TransposeNumbers[j]))
                        reg[k][i, j] =RegFactors[i,k,TransposeNumbers[j]];            
                        used=true                                                                                    
                    end
                    if used==false
                        @show (i,j, k)
                        println(TransposeNumbersUnique)
                        println("CONCEPTUAL ERROR")
                        return
                    end
                end
            end
        end





    end
    reg, factors
end