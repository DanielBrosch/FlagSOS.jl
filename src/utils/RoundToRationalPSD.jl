using LinearAlgebra, GenericLinearAlgebra

function roundRationalPSD(A; baseType = BigInt, prec = 1e-5)
    if size(A,1) == 1
        return (psd = max(rationalize(baseType, A[1,1]), Rational{baseType}(0//1)),)
    end
    eg = eigen(Hermitian(A))
    egVals = eg.values#rationalize.(baseType, eg.values; tol = prec)#; digits = digits)
    posInds = egVals .> 0 

    egVals[.!posInds] .= 0

    cholesky = eg.vectors * Diagonal(sqrt.(egVals))
    @show cholesky 
    cholesky = rationalize.(baseType, cholesky; tol = prec)
    @show cholesky 

    # egVecs = rationalize.(baseType, eg.vectors; tol = prec)#; digits = digits)
    # @show egVals 
    # @show egVecs
    # return egVecs[:, posInds] * diagm(egVals[posInds]) * egVecs[:, posInds]'
    return (psd = cholesky * cholesky', chol = cholesky)

end