export QuantumFlag

"""
$(TYPEDEF)

A linear combination of Flags of type `F` with coefficients of type `T`.
"""
mutable struct QuantumFlag{F<:Flag,T}
    coeff::Dict{F,T}

    QuantumFlag{F,T}(cs::Dict{F,T}) where {F<:Flag,T} = new(cs)
    QuantumFlag{F,T}(opts...) where {F<:Flag,T} = new(Dict{F,T}(opts...))
    QuantumFlag{F}(fc::QuantumFlag{F,T}) where {F<:Flag,T} = new{F,T}(fc.coeff)
end

function Base.promote_rule(
    ::Type{QuantumFlag{F,T}}, ::Type{QuantumFlag{F,U}}
) where {F<:Flag,T,U}
    return QuantumFlag{F,promote_type(T, U)}
end

function Base.show(io::IO, Fs::QuantumFlag)
    first = true
    for (g, c) in Fs.coeff
        if c < 0 || (first && c > 0)
            print(io, " $c $g")
            first = false
        else
            print(io, " + $c $g ")
        end
    end
end

function Base.zero(::QuantumFlag{F,T}) where {F<:Flag,T<:Real}
    return QuantumFlag{F,T}()
end

function ==(F1::QuantumFlag{F,T}, F2::QuantumFlag{F,T}) where {F<:Flag,T<:Real}
    return F1.coeff == F2.coeff
end

"""
    size(F::QuantumFlag) 

The maximum size of the Flags in 'F'.
"""
function Base.size(F::QuantumFlag)
    length(F.coeff) == 0 && return 0

    return maximum([size(f) for f in keys(F.coeff)])
end

"""
    countEdges(F::QuantumFlag) 

The maximum number of edges of the flags in 'F'.
"""
function countEdges(F::QuantumFlag)
    length(F.coeff) == 0 && return 0

    return maximum([countEdges(f) for f in keys(F.coeff)])
end

"""
    :*(F::QuantumFlag{T,R}, G::QuantumFlag{T, R}) where {T <: Flag, R<:Real}

The gluing operation of type `T` extended to linear combinations of Flags.
"""
function Base.:*(F::QuantumFlag{T,R}, G::QuantumFlag{T,R}) where {T<:Flag,R<:Real}
    res = QuantumFlag{T,R}()
    for (A, c) in F.coeff
        for (B, d) in G.coeff
            AB = A * B
            if AB isa QuantumFlag
                for (C, e) in AB.coeff
                    res.coeff[C] = get(res.coeff, C, zero(R)) + c * d * e
                end
            else
                res.coeff[AB] = get(res.coeff, AB, zero(R)) + c * d
            end
        end
    end

    filter!(p -> !iszero(p.second), res.coeff)
    return res
end

"""
    :*(c::R, G::QuantumFlag{T, R}) where {T <: Flag, R<:Real}

Scalar multiplication of a linear combinations of Flags.
"""
function Base.:*(c::R1, G::QuantumFlag{T,R2}) where {T<:Flag,R1<:Real, R2<:Real}
    R = promote_type(R1, R2)
    return QuantumFlag{T,R}(Dict(g => c * d for (g, d) in G.coeff))
end

"""
    :*(c::R, G::T) where {T <: Flag, R<:Real}

Scalar multiplication of Flags. Returns a 'QuantumFlag{T, R}'.
"""
function Base.:*(c::R, G::T) where {T<:Flag,R<:Real}
    return QuantumFlag{T,R}(Dict(G => c))
end

"""
    :-(G::T) where {T <: Flag}

Scalar multiplication of Flags. Returns a 'QuantumFlag{T, Int}'.
"""
function Base.:-(G::T) where {T<:Flag}
    return QuantumFlag{T,Int}(Dict(G => -1))
end

"""
    :+(F::QuantumFlag{T,R}, G::QuantumFlag{T, R}) where {T <: Flag, R<:Real}

Adds two linear combinations of Flags.
"""
function Base.:+(F::QuantumFlag{T,R1}, G::QuantumFlag{T,R2}) where {T<:Flag,R1<:Real, R2<:Real}
    R = promote_type(R1, R2)
    res = QuantumFlag{T,R}(mergewith(+, F.coeff, G.coeff))

    filter!(p -> !iszero(p.second), res.coeff)
    return res
end

"""
    :+(F::T, G::QuantumFlag{T, R}) where {T <: Flag, R<:Real}

Adds a flag to a linear combination of flags.
"""
function Base.:+(F::T, G::QuantumFlag{T,R}) where {T<:Flag,R<:Real}
    return 1 * F + G
end
function Base.:+(F::QuantumFlag{T,R}, G::T) where {T<:Flag,R<:Real}
    return F + 1 * G
end
function Base.:-(F::T, G::QuantumFlag{T,R}) where {T<:Flag,R<:Real}
    return 1 * F - G
end
function Base.:-(F::QuantumFlag{T,R}, G::T) where {T<:Flag,R<:Real}
    return F - 1 * G
end
function Base.:+(t::R1, G::QuantumFlag{T,R2}) where {T<:Flag,R1<:Real, R2<:Real}
    return t*one(T) + G
end

"""
    :+(F::T, G::T) where {T <: Flag}

Adds two Flags. Returns a 'QuantumFlag{T, Int}'.
"""
function Base.:+(F::T, G::T) where {T<:Flag}
    if F == G
        return QuantumFlag{T,Int}(F => 2)
    else
        return QuantumFlag{T,Int}(F => 1, G => 1)
    end
end

"""
    :-(F::T, G::T) where {T <: Flag}

Subtracts two Flags. Returns a 'QuantumFlag{T, Int}'.
"""
function Base.:-(F::T, G::T) where {T<:Flag}
    if F == G
        return QuantumFlag{T,Int}()
    else
        return QuantumFlag{T,Int}(F => 1, G => -1)
    end
end

"""
    :-(F::QuantumFlag{T,R}) where {T <: Flag, R<:Real}

Inverts the sign of a linear combinations of Flags.
"""
function Base.:-(F::QuantumFlag{T,R}) where {T<:Flag,R<:Real}
    res = QuantumFlag{T,R}(Dict(g => -c for (g, c) in F.coeff))
    return res
end

"""
    :-(F::QuantumFlag{T,R}, G::QuantumFlag{T, R}) where {T <: Flag, R<:Real}

Subtracts two linear combinations of Flags.
"""
function Base.:-(F::QuantumFlag{T,R1}, G::QuantumFlag{T,R2}) where {T<:Flag,R1<:Real, R2<:Real}
    res = F + (-G)

    filter!(p -> !iszero(p.second), res.coeff)
    return res
end

"""
    :*(F::T, G::QuantumFlag{T, R}) where {T <: Flag, R<:Real}

The gluing operation of type `T` extended to linear combinations of Flags.
"""
function Base.:*(F::T, G::QuantumFlag{T,R}) where {T<:Flag,R<:Real}
    res = QuantumFlag{T,R}()
    for (B, d) in G.coeff
        AB = F * B
        AB === nothing && continue
        res.coeff[AB] = get(res.coeff, AB, zero(R)) + d
    end

    filter!(p -> !iszero(p.second), res.coeff)
    return res
end

"""
    :*(G::QuantumFlag{T, R},F::T) where {T <: Flag, R<:Real}

The gluing operation of type `T` extended to linear combinations of Flags.
"""
function Base.:*(G::QuantumFlag{T,R}, F::T) where {T<:Flag,R<:Real}
    return F * G
end

"""
    labelCanonically(F::QuantumFlag{T,R})::QuantumFlag{T,R} where {T <: Flag, R <: Real}

Labels `F` canonically. If two Flags are isomorphic, this function should return the same Flag.
"""
function labelCanonically(F::QuantumFlag{T,R})::QuantumFlag{T,R} where {T<:Flag,R<:Real}
    labeled = labelCanonically(collect(keys(F.coeff)))

    res = QuantumFlag{T,R}()

    for (i, (F, c)) in enumerate(F.coeff)
        res.coeff[labeled[i]] = get(res.coeff, labeled[i], 0) + c
    end

    filter!(p -> !iszero(p.second), res.coeff)

    return res
end

function removeIsolated(F::QuantumFlag{T,D}) where {T<:Flag,D}
    res = QuantumFlag{T,D}()

    for (f, c) in F.coeff
        isoV = isolatedVertices(f)
        # @show isoV
        if any(isoV)
            fIso = subFlag(f, .!isoV)
        else
            fIso = f
        end
        res.coeff[fIso] = get(res.coeff, fIso, zero(D)) + c
    end

    return res
end

import Base.convert

function Base.convert(
    ::Type{QuantumFlag{T,D}},
    F::QuantumFlag{T,D2},
) where {T<:Flag, D, D2}
    return QuantumFlag{T,D}(
        F.coeff
    )
end