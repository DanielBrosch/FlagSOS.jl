using LinearAlgebra
using Combinatorics

# For keeping track of "marked" edges
# Speeds up generation of flags up to isomorphism, as well as Moebius-transforms
struct EdgeMarkedFlag{T} <: Flag
    F::T
    marked::Set{Predicate}
    EdgeMarkedFlag{T}(F::T) where {T<:Flag} = new(F, Set())
    EdgeMarkedFlag{T}(F::T, marked::Set) where {T<:Flag} = new(F, marked)
    function EdgeMarkedFlag{T}(F::T, marked::Vector{Vector{P}}) where {T<:Flag,P<:Predicate}
        return new(F, Set(vcat(marked...)))
    end
    function EdgeMarkedFlag{T}(F::T, marked::Vector{Vector}) where {T<:Flag}
        return new(F, Set(vcat(marked...)))
    end
    function EdgeMarkedFlag{T}(F::T, marked::Vector{P}) where {T<:Flag,P<:Predicate}
        return new(F, Set(marked))
    end
end

function ==(A::EdgeMarkedFlag, B::EdgeMarkedFlag)
    return A.F == B.F && A.marked == B.marked
end
function hash(A::EdgeMarkedFlag, h::UInt)
    return hash(A.marked, hash(A.F, hash(:EdgeMarkedFlag, h)))
end

Base.one(::Type{EdgeMarkedFlag{T}}) where {T} = EdgeMarkedFlag{T}(one(T), Set())

function size(G::EdgeMarkedFlag)::Int
    return size(G.F)
end

function findUnknownPredicates(
    F::EdgeMarkedFlag, fixed::Vector{U}
) where {U<:AbstractVector{Int}}
    return findUnknownPredicates(F.F, fixed)
end

function isAllowed(G::EdgeMarkedFlag)
    return isAllowed(G.F)
end

function addPredicates(G::EdgeMarkedFlag{T}, preds::Vector{P}) where {T<:Flag,P<:Predicate}
    return EdgeMarkedFlag{T}(addPredicates(G.F, preds), G.marked)
end

function permute(F::EdgeMarkedFlag{T}, p::AbstractVector{Int}) where {T<:Flag}
    return EdgeMarkedFlag{T}(permute(F.F, p), Set(permute(e, p) for e in F.marked))
end

function maxPredicateArguments(::Type{EdgeMarkedFlag{T}}) where {T<:Flag}
    return maxPredicateArguments(T)
end

function distinguish(F::EdgeMarkedFlag, v::Int, W::BitVector)
    return (distinguish(F.F, v, W), sort!([distinguish(m, v, W) for m in F.marked]))
end

function countEdges(F::EdgeMarkedFlag)::Vector{Int}
    return vcat(countEdges(F.F), [length(F.marked)])
end

function isolatedVertices(F::EdgeMarkedFlag)
    return BitVector([false for i in 1:size(F)])
end

function allWaysToAddOneMarked(F::EdgeMarkedFlag{T}) where {T<:Flag}
    res = Dict{EdgeMarkedFlag{T},Int}()
    for e in F.marked
        added = addPredicates(F.F, [e])
        if added !== nothing
            markedN = filter!(x -> isAllowed(added, x), setdiff(F.marked, [e]))
            Fn = EdgeMarkedFlag{T}(added, markedN)
            Fl = labelCanonically(Fn)
            res[Fl] = get(res, Fl, 0) + 1
        end
    end
    return res
end

"""
    moebius(F::T, verts = 1:size(F)) where {T<:Flag}

Computes the moebius transform of a flag on the vertices 'verts'
"""
function moebius(F::T, verts=1:size(F)) where {T<:Flag}
    @assert verts == 1:size(F) "TODO"
    markedF = EdgeMarkedFlag{T}(F, findUnknownPredicates(F))
    return moebius(markedF)
end

function vertexColor(F::EdgeMarkedFlag{T}, v::Int) where {T<:Flag}
    return vertexColor(F.F, v)
end

"""
    moebius(F::EdgeMarkedFlag{T}) where {T<:Flag}

Computes the moebius transform of an edge-marked flag on the marked edges. 
"""
function moebius(F::EdgeMarkedFlag{T}) where {T<:Flag}
    res = 0 * F.F
    k = length(F.marked)
    if k == 0
        return 1 * F.F
    end

    tmp = Dict{EdgeMarkedFlag{T},Int}(F => 1)
    tmp2 = Dict{EdgeMarkedFlag{T},Int}()

    for flippedEdges in 0:k
        for (F2, c2) in tmp
            res += c2 * (-1)^flippedEdges * F2.F
            for (F3, c3) in allWaysToAddOneMarked(F2)
                tmp2[F3] = get(tmp2, F3, 0) + c2 * c3
            end
        end
        map!(x -> Int(x//(flippedEdges + 1)), values(tmp2))
        tmp = deepcopy(tmp2)

        empty!(tmp2)
    end

    return res
end

function zeta(F::EdgeMarkedFlag{T}) where {T<:Flag}
    res = moebius(F)
    map!(abs, values(res.coeff))
    return res
end

function moebius(Fs::QuantumFlag{EdgeMarkedFlag{T},D}) where {T<:Flag,D}
    if length(Fs.coeff) == 0
        return QuantumFlag{T,D}()
    end

    k = maximum(length(F.marked) for F in keys(Fs.coeff))

    tmp = Dict{EdgeMarkedFlag{T},D}(F => c for (F, c) in Fs.coeff)

    tmp2 = Dict{EdgeMarkedFlag{T},D}()
    res = QuantumFlag{T,D}()

    for flippedEdges in 0:k
        for (F2, c2) in tmp
            res += c2 * (-1)^flippedEdges * F2.F

            for (F3, c3) in allWaysToAddOneMarked(F2)
                tmp2[F3] = get(tmp2, F3, 0) + c2 * c3
            end
        end
        map!(x -> D(x//(flippedEdges + 1)), values(tmp2))
        tmp = deepcopy(tmp2)

        empty!(tmp2)
    end
    return res
end
