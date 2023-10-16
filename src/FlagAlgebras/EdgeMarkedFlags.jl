using LinearAlgebra
using Combinatorics

# For keeping track of "marked" edges
# Speeds up generation of flags up to isomorphism, as well as Moebius-transforms
# struct EdgeMarkedFlag{T, P} <: Flag
#     F::T
#     marked::Set{P}
#     EdgeMarkedFlag{T}(F::T) where {T<:Flag} = new{T, predicateType(T)}(F, Set{predicateType(T)}())
#     # EdgeMarkedFlag{T}(F::T, marked::Set) where {T<:Flag} = new{T, predicateType(T)}(F, Set{predicateType(T)}(marked))
#     EdgeMarkedFlag{T}(F::T, marked::Set) where {T<:Flag} = new{T, predicateType(T)}(F, marked)
#     function EdgeMarkedFlag{T}(F::T, marked::Vector{Vector{P}}) where {T<:Flag, P<:Predicate}
#         return new{T, predicateType(T)}(F, Set{predicateType(T)}(vcat(marked...)))
#     end
#     function EdgeMarkedFlag{T}(F::T, marked::Vector{Vector}) where {T<:Flag}
#         return new{T, predicateType(T)}(F, Set{predicateType(T)}(vcat(marked...)))
#     end
#     function EdgeMarkedFlag{T}(F::T, marked::Vector{P}) where {T<:Flag,P<:Predicate}
#         return new{T, predicateType(T)}(F, Set{predicateType(T)}(marked))
#     end
# end

struct EdgeMarkedFlag{T, P} <: Flag
    F::T
    marked::Vector{P}
    EdgeMarkedFlag{T}(F::T) where {T<:Flag} = new{T, predicateType(T)}(F, Vector{predicateType(T)}())
    EdgeMarkedFlag{T}(F::T, marked::Vector) where {T<:Flag} = new{T, predicateType(T)}(F, marked)
    function EdgeMarkedFlag{T}(F::T, marked::Vector{Vector{P}}) where {T<:Flag, P<:Predicate}
        return new{T, predicateType(T)}(F, vcat(marked...))
    end
    function EdgeMarkedFlag{T}(F::T, marked::Vector{Vector}) where {T<:Flag}
        return new{T, predicateType(T)}(F, vcat(marked...))
    end
    function EdgeMarkedFlag{T}(F::T, marked::Vector{P}) where {T<:Flag,P<:Predicate}
        return new{T, predicateType(T)}(F, marked)
    end
end

function ==(A::EdgeMarkedFlag, B::EdgeMarkedFlag)
    return A.F == B.F && Set(A.marked) == Set(B.marked)
end
function hash(A::EdgeMarkedFlag, h::UInt)
    return hash(Set(A.marked), hash(A.F, hash(:EdgeMarkedFlag, h)))
end

Base.one(::Type{EdgeMarkedFlag{T,P}}) where {T, P} = EdgeMarkedFlag{T}(one(T), Vector{P}())

function size(G::EdgeMarkedFlag)::Int
    return size(G.F)
end

function findUnknownPredicates(
    F::EdgeMarkedFlag, fixed::Vector{U}
) where {U<:AbstractVector{Int}}
    return findUnknownPredicates(F.F, fixed)
end

function predicateType(::Type{EdgeMarkedFlag{T,P}}) where {T<:Flag,P}
    return predicateType(T)
end

function isAllowed(G::EdgeMarkedFlag)
    return isAllowed(G.F)
end

function isAllowed(G::EdgeMarkedFlag{T,P}, e::P) where {T,P}
    return isAllowed(G.F, e)
end

function addPredicates(G::EdgeMarkedFlag{T,P}, preds::Vector{Q}) where {T<:Flag, P, Q<:Predicate}
    return EdgeMarkedFlag{T, predicateType(T)}(addPredicates(G.F, preds), G.marked)
end

function permute(F::EdgeMarkedFlag{T,P}, p::AbstractVector{Int}) where {T<:Flag, P<:Predicate}
    return EdgeMarkedFlag{T}(permute(F.F, p), P[permute(e, p) for e in F.marked])
end

function maxPredicateArguments(::Type{EdgeMarkedFlag{T,P}}) where {T<:Flag, P<:Predicate}
    return maxPredicateArguments(T)
end

function distinguish(F::EdgeMarkedFlag, v::Int, W::BitVector)::UInt
    # return hash(distinguish(F.F, v, W), hash(sort!(UInt[distinguish(m, v, W) for m in F.marked])))
    tmp::UInt = hash(:EdgeMarkedFlag)
    for m in F.marked
        tmp ⊻= distinguish(m, v, W)
    end
    return hash(distinguish(F.F, v, W), tmp)
    # return hash(distinguish(F.F, v, W), reduce(⊻, distinguish(m, v, W) for m in F.marked; init = hash(:EdgeMarkedFlag)))
end

function countEdges(F::EdgeMarkedFlag)::Vector{Int}
    return vcat(countEdges(F.F), [length(F.marked)])
end

function isolatedVertices(F::EdgeMarkedFlag)
    return BitVector([false for i in 1:size(F)])
end

function allWaysToAddOneMarked(F::EdgeMarkedFlag{T,P}) where {T<:Flag, P<:Predicate}
    res = Dict{EdgeMarkedFlag{T,P},Int}()
    for e in F.marked
        added = addPredicates(F.F, [e])
        if added !== nothing
            markedN = P[p for p in F.marked if p != e && isAllowed(added, p)]
            # markedN = setdiff(F.marked, [e])#filter!(x -> isAllowed(added, x), setdiff(F.marked, [e]))
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

"""
    zeta(F::T, verts = 1:size(F)) where {T<:Flag}

Computes the zeta transform of a flag on the vertices 'verts'
"""
function zeta(F::T, verts=1:size(F)) where {T<:Flag}
    @assert verts == 1:size(F) "TODO"
    markedF = EdgeMarkedFlag{T}(F, findUnknownPredicates(F))
    return zeta(markedF)
end

function zeta(F::QuantumFlag{T,D}) where {T<:Flag, D}
    tmp = sum(c*EdgeMarkedFlag{T}(G, findUnknownPredicates(G)) for (G,c) in F.coeff)
    return zeta(tmp)
end

function moebius(F::QuantumFlag{T,D}) where {T<:Flag, D}
    tmp = sum(c*EdgeMarkedFlag{T}(G, findUnknownPredicates(G)) for (G,c) in F.coeff)
    return moebius(tmp)
end

function vertexColor(F::EdgeMarkedFlag{T,P}, v::Int) where {T<:Flag, P<:Predicate}
    return vertexColor(F.F, v)
end

"""
    moebius(F::EdgeMarkedFlag{T}) where {T<:Flag}

Computes the moebius transform of an edge-marked flag on the marked edges. 
"""
function moebius(F::EdgeMarkedFlag{T, P}) where {T<:Flag, P<:Predicate}
    res = 0 * F.F
    k = length(F.marked)
    if k == 0
        return 1 * F.F
    end

    tmp = Dict{EdgeMarkedFlag{T,P},Int}(F => 1)
    tmp2 = Dict{EdgeMarkedFlag{T,P},Int}()

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

function zeta(F::QuantumFlag{EdgeMarkedFlag{T, P},D}) where {T<:Flag, D, P<:Predicate}
    res = moebius(F)
    map!(abs, values(res.coeff))
    return res
end

function zeta(F::EdgeMarkedFlag{T,P}) where {T<:Flag, P<:Predicate}
    res = moebius(F)
    map!(abs, values(res.coeff))
    return res
end

function moebius(Fs::QuantumFlag{EdgeMarkedFlag{T, P},D}) where {T<:Flag,D, P<:Predicate}
    if length(Fs.coeff) == 0
        return QuantumFlag{T,D}()
    end

    k = maximum(length(F.marked) for F in keys(Fs.coeff))

    tmp = Dict{EdgeMarkedFlag{T,P},D}(F => c for (F, c) in Fs.coeff)

    tmp2 = Dict{EdgeMarkedFlag{T,P},D}()
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