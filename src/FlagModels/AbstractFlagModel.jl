export modelSize, computeSDP!, modelBlockSizes, buildJuMPModel

"""
    AbstractFlagModel{T<:Flag, N, D}

An abstract Flag-SOS model. `T` is the Flag-type used internally, i.e. as variables in the SDP obtained at the end. It may be advantageous to use non-induced Flags internally, even when the model is formulated with induced Flags.

`N` is either `:limit`, `:variable` or an Integer. If `N == :limit`, then we are in the usual case of Flag Algebras, i.e. the case where the number of vertices goes towards infinity (fastest). If `N` is an integer, then we are in the case of exactly `N` vertices (slower). If `N == :variable`, then the model will be parametrized by a variable, i.e. coefficients will be polynomials in `N` (slowest).

`D` is the datatype for the coefficients in the final optimization problem.
"""
abstract type AbstractFlagModel{T<:Flag,N,D} end

function modelSize(m::T) where {T<:AbstractFlagModel}
    error("modelSize not implemented for $T")
    return missing
end

function modelBlockSizes(m::T) where {T<:AbstractFlagModel}
    error("modelBlockSizes not implemented for $T")
    return missing
end


function computeSDP!(m::T) where {T<:AbstractFlagModel}
    error("computeSDP! not implemented for $T")
    return missing
end

"Returns (Variables, Constraints)"
function buildJuMPModel(m::T) where {T<:AbstractFlagModel}
    error("buildJuMPModel not implemented for $T")
    return missing
end

include("FlagModel.jl")
include("LasserreModel.jl")
include("QuadraticModule.jl")
include("RazborovModel.jl")