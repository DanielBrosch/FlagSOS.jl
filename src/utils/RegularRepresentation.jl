
function randElement(P::Matrix{Int})
    n = maximum(P)
    cs = randn(n)
    A = [cs[i] for i in P]
    return A
end

function checkAlgebra(P::Matrix{Int})
    A, B = randElement(P), randElement(P)
    C = A*B
    for i = 1:maximum(P)
        cs = unique(C[P .== i])
        cs = unique(round.(cs, digits = 4))
        if length(cs) > 1 
            return false 
        end
    end
    return true        
end

function tr3(A,B,C)
    n = size(A,1)
    res = zero(Int)
    for i = 1:n, j = 1:n, k = 1:n
        res += A[i,j]*B[j,k]*C[k,i]
    end
    return res
end

function regularRepresentation(P::Matrix{Int})

    n = maximum(P)
    @assert checkAlgebra(P) "The partition given by the entries of P have to correspond to a Matrix-*-Algebra!"

    As = Dict(i => sparse(Int.(P .== i)) for i = 1:maximum(P))

    # As(i) = Int.(P .== i)

    factors = Dict(i => 1 / sqrt(dot(As[i], As[i])) for i = 1:n)
    # factors = Dict(i => 1 / sqrt(dot(As(i), As(i))) for i = 1:n)

    reg = Dict(k => zeros(Float64, n, n) for k = 1:n)

    BiBj = zeros(Int, size(P))

    for i = 1:n
        for j = 1:n
            @show (i,j, n)
            # BiBj = As(i) * As(j)'
            BiBj .= As[i] * As[j]'
            # @show (i,j, n)
            for k = 1:n
                # reg[k][i, j] = factors[i] * factors[j] * factors[k] * tr3(As[i], As[j]', As[k]')
                reg[k][i, j] = factors[i] * factors[j] * factors[k] * dot(BiBj, As[k]')
                # reg[k][i, j] = factors[i] * factors[j] * factors[k] * dot(BiBj, As(k)')
            end
        end
    end
    reg, factors
end