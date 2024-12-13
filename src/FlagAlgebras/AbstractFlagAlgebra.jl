# module FlagAlgebras

using DocStringExtensions
using Combinatorics
using Memoize # for isIsomorphic. Replace with more efficient algorithm later?

export Flag, labelCanonically, aut, glue, permute, countEdges
import Base.zero
import Base.==
import Base.one
import Base.size
import Base.hash

include("PartitionOverlaps.jl") # for finite and variable n support

""" 
    $(TYPEDEF)

An abstract Flag.
"""
abstract type Flag end

include("QuantumFlags.jl") # Formal linear combinations of flags

"""
    $(TYPEDEF)

A way to describe one predicate value in a Flag. For example, it may describe a single edge of a `Graph`, or a single label of a `PartiallyLabeledFlag`.
"""
abstract type Predicate end

"""
    possibleValues(::Type{P}) where {P<:Predicate}

Returns the possible non-zero (!) values of a predicate of type `P`. Usually just `[true]`, but for example directed graphs (without possiblity of a bi-directional edge) may have predicate values 0, 1 and -1.
"""
function possibleValues(predicateType::Type{P})::Vector{Int} where {P<:Predicate}
    return [true]
end

function permute(pred::P, p::AbstractVector{Int}) where {P<:Predicate}
    error("permuting predicates of type $P is not implemented!")
    return nothing
end

# Optional third and fourth argument: flag which this predicate is permuted with, before and after. Does potentially change the color in colorblind EdgeColoredGraphs
function permute(pred::P, p::AbstractVector{Int}, ::T, ::T) where {P<:Predicate,T<:Flag}
    return permute(pred, p)
end

"""
    addPredicates(::T, ::U, ::Vararg{U} where {T<:Flag,U<:Predicate}

Creates a copy of `F`, and adds all predicates with the given values to the copy. May change the order of vertices of `F`, if necessary (E.g. in the case of `PartiallyLabeledFlag`). The predicates are given as a Vector of Vectors of Predicate-value pairs, sorted by type in a way that `addPredicates` understands.
"""
function addPredicates(::T, ::Vector) where {T<:Flag}
    error("addPredicates is not defined for Flag type $T")
    return missing
end
function addPredicates(F::T) where {T<:Flag}
    return F
end

function ==(A::T, B::T) where {T<:Flag}
    error("Missing comparison operator for $(T)")
    return true
end
function hash(A::T, h::UInt) where {T<:Flag}
    error("Missing hash function for $(T)")
    return hash(:T, h)
end

"""
    one(F::T)::T where {T <: Flag}

The empty Flag of the same type as `F`.
"""
function Base.one(::T)::T where {T<:Flag}
    return one(T)
end

"""
    one(F::Type{T})::T where {T <: Flag}

The empty Flag of type `T`.
"""
function Base.one(::Type{T})::T where {T<:Flag}
    error("one is not defined for Flag type $T")
    return missing
end

"""
    size(F::T)::Int where {T<:Flag}

The size (number of vertices) of `F`.
"""
function Base.size(F::T)::Int where {T<:Flag}
    error("size is not defined for Flag type $T")
    return missing
end

"""
    :*(F::T, G::T) where {T<:Flag}

The gluing operation of type `T`. Should, for example, glue unlabeled vertices to distinct vertices in the result. Default implementation glues the Flags on fully distinct vertices.
"""
function Base.:*(F::T, G::T; isAllowed=(f) -> true) where {T<:Flag}
    n = size(F)
    m = size(G)
    return glue(F, G, vcat((m + 1):(m + n), 1:m); isAllowed=isAllowed)
end

"""
    aut(F::T)::NamedTuple{(:gen, :size),Tuple{Vector{Vector{Int64}},Int64}} where {T<:Flag}

The automorphisms of `F`. Returns a named tuple with fields
* `gen::Vector{Vector{Int}}`: Vector of permutations generating all automorphisms.
* `size::Int`: The size of the automorphism group of `F`.
"""
function aut(
    F::T
)::NamedTuple{(:gen, :size),Tuple{Vector{Vector{Int64}},Int64}} where {T<:Flag}
    grp = label(F; removeIsolated=false)[3]
    return (gen=grp.gen, size=order(grp))
end

"""
    labelCanonically(F::T)::T where {T <: Flag}

Labels `F` canonically. If two Flags are isomorphic, this function should return the same Flag.
"""
function labelCanonically(F::T)::T where {T<:Flag}
    return label(F)[1]
end

"""
    labelCanonically(Fs::Vector{T})::Vector{T} where {T <: Flag}

Labels all Flags in `Fs` canonically. If two Flags are isomorphic, this function should return the same Flag.
"""
function labelCanonically(Fs::Vector{T})::Vector{T} where {T<:Flag}
    return labelCanonically.(Fs)
end

"""
    glue(F::T, G::T, p::Vector{Int})::U where {T<:Flag, U<:Flag}

Glues together the two Flags `F` and `G`, after applying the permutation `p` to the vertices of `F`. `p` may be a permutation involving more than `size(F)` vertices, in which case the result should have at least `maximum(p)` vertices. Optionally specifices a different output Flag type, for cases where the internal Flag type differs and there are performance advantages (such as the case of internal non-induced Graphs and the gluing of two induced Graphs).
"""
function glue(F::T, G::T, p::AbstractVector{Int}; isAllowed=(f) -> true) where {T<:Flag}
    error("glue is not defined for Flag type $T with target type $T")
    return missing
end

"""
    glue(Fs::Vararg{T}) where {T<:Flag}

Glues Flags together "on top of each other". Optionally specifices the output Flag type, for cases where a different type may improve performance (E.g. non-induced Flag as target for the gluing of two induced Flags). The default implementation only uses the custom type for the final gluing.

    glue(F, G, H)

is equivalent to

    glue(F, glue(G, H, 1:size(G)), 1:size(F))
"""
function glue(Fs::Vararg{T}; isAllowed=(f) -> true) where {T<:Flag}
    if length(Fs) == 1
        return Fs[1]
    elseif length(Fs) == 2
        return glue(Fs..., 1:size(Fs[1]); isAllowed=isAllowed)
    end
    @views return glue(
        Fs[1], glue(Fs[2:end]...; isAllowed=isAllowed), 1:size(Fs[1]); isAllowed=isAllowed
    )
end

glue() = nothing

"""
    glueFinite(N, F::T, G::T, p::AbstractVector{Int}; labelFlags = true) where {T<:Flag}

Glues together the flags `F` and `G`, after applying the permutation `p` to the vertices of `F`. This variant of `glue` is for optimizing over finite objects, given by `N` which should be one of the options `:limit`, `:variable` or an integer. The operation assumes the k vertices that are sent on top of each other by `p` correspond to labels, and assumes that the other vertices are unlabeled, i.e. get sent to all `N-k` other vertices. 
"""
function glueFinite(
    N,
    F::T,
    G::T,
    p::AbstractVector{Int}=vcat(collect((size(G) + 1):(size(G) + size(F))), 1:size(G));
    labelFlags=true,
    isAllowed=(f) -> true,
) where {T<:Flag}
    return glueFinite_internal(N, F, G, p; labelFlags=labelFlags, isAllowed=isAllowed)
end

function glueFinite_internal(
    N, F::T, G::T, p::AbstractVector{Int}; labelFlags=true, isAllowed=(f) -> true
) where {T<:Flag}
    if N == :limit
        res = glue(F, G, p; isAllowed=isAllowed)
        if res === nothing
            return QuantumFlag{T,Rational{Int64}}()
        end
        if labelFlags
            return labelCanonically(res)
        end
        return res
    end
    if N == :variable
        error("Variable n not implemented right now!")
    end

    @assert N isa Int

    # G has vertices 1:size(G)
    # F has vertices p[1:size(F)]

    labelsF = [i for i in 1:size(F) if p[i] <= size(G)]
    labelsG = intersect(1:size(G), p[1:size(F)])

    @assert length(labelsF) == length(labelsG)

    k = length(labelsF)

    freeF = setdiff(1:size(F), labelsF)
    freeG = setdiff(1:size(G), labelsG)

    if length(freeF) == 0 || length(freeG) == 0
        tmp = glue(F, G, p; isAllowed=isAllowed)
        if tmp === nothing
            return QuantumFlag{T,Rational{Int}}()
        end
        if labelFlags
            return 1//1 * labelCanonically(tmp)
        end
        return 1//1 * tmp
    end

    freePositions = N - k

    lambda::Vector{Int} = repeat([1], length(freeF))
    mu::Vector{Int} = repeat([1], length(freeG))

    ovs = overlaps(lambda, mu, freePositions, false, true)

    factor = 1//sum(x for (x, _) in ovs; init=0)

    res = QuantumFlag{T,Rational{Int}}()

    for (c, o) in ovs
        po = deepcopy(p)
        for pos in findall(o .== 1)
            j, i = Tuple(pos)
            i == length(freeF) + 1 && continue
            j == length(freeG) + 1 && continue

            # po[freeG[j]] = freeF[i]
            # @show po 
            # @show freeF 
            # @show freeF[i]
            # @show freeG 
            # @show freeG[j]
            po[freeF[i]] = freeG[j]
        end
        newG = glue(F, G, po; isAllowed=isAllowed)
        if newG !== nothing
            res += c * factor * newG
        end
    end

    if labelFlags
        return labelCanonically(res)
    else
        return res
    end
end

function glueFinite(N, F::T, G::QuantumFlag{T,D}; isAllowed=(f) -> true) where {T,D}
    return sum(c * glueFinite(N, F, g; isAllowed=isAllowed) for (g, c) in G.coeff)
end

"""
    permute(F::T, p::AbstractVector{Int})::T where {T<:Flag}

Permutes the vertices of `F` according to the permutation `p`.
"""
function permute(F::T, p::AbstractVector{Int}) where {T<:Flag}
    return glue(F, one(T), p)
end

"""
    isSym(F::T, v1::Int, v2::Int)::Bool where {T<:Flag}

Returns true if the permutation which swaps the vertices `v1` and `v2` is an automorphism of `F`.
"""
function isSym(F::T, v1::Int, v2::Int)::Bool where {T<:Flag}
    error("isSym is not defined for Flag type $T")
    return missing
end

"""
    subFlag(F::T, vertices::AbstractVector{Int})::T where {T<:Flag}

Returns the sub-Flag indexed by `vertices`, which is a subset of `1:size(F)`.
"""
function subFlag(F::T, vertices::AbstractVector{Int})::T where {T<:Flag}
    error("subFlag is not defined for Flag type $T")
    return missing
end

"""
    subFlag(F::T, vertices::BitVector)::T where {T<:Flag}

Returns the sub-Flag given by the indicator vector `vertices`, which is a `BitVector` of length `size(F)`. If not extended, it calls `subFlag(F, findall(vertices))`.
"""
function subFlag(F::T, vertices::BitVector)::T where {T<:Flag}
    return subFlag(F, findall(vertices))
end

"""
    findUnknownPredicates(F::T, fixed::Vector{Vector{Int}})

Given a Flag `T`, as well as subsets of vertices such that predicates (e.g. edges) are fixed if all arguments are within one of these sets. One should return a `Predicate` for each predicate and each combination of arguments, such that not all arguments are contained in one of the fixed subsets. The function returns a Vector of Vectors of Predicates, such that  should return a Vector of Vectors of Predicates `addPredicates` can understand it.

This is then used to determine the glued Flag in induced settings. For example, gluing the partially labelled edge 1-o to itself, would call

    findUnknownPredicates(Graph(Bool[0 1 1; 1 0 0; 1 0 0]), [[1,2],[1,3]])

The only unclear predicate here is the edge [2,3], i.e. this function should return

    [[EdgePredicate(2,3)]]
"""
function findUnknownPredicates(
    F::T, fixed::Vector{U}=Vector{Int}[], predLimits::Vector=Int[]
) where {T<:Flag,U<:AbstractVector{Int}}
    error("findUnknownPredicates is not defined for Flag type $T")
    return nothing
end

function findUnknownGenerationPredicates(
    F::T, fixed::Vector{U}=Vector{Int}[], predLimits::Vector=Int[]
) where {T<:Flag,U<:AbstractVector{Int}}
    return predicateType(T)[]
end

"""
    countEdges(F::T)::Vector{Int} where {T<:Flag}


Returns the Vector of numbers of set predicates in the Flag `F` for each `Predicate` type. For Graphs, this is the Vector with one element, the number of edges in the graph. Used when generating all Flags up to isomorphism of a given type to specify an upper bound on the number of set predicates.
"""
function countEdges(F::T)::Vector{Int} where {T<:Flag}
    error("countEdges is not defined for Flag type $T")
    return missing
end

"""
    isolatedVertices(F::T)::BitVector where{T<:Flag}

Returns the indicator vector of isolated vertices of `F`.
"""
function isolatedVertices(F::T)::BitVector where {T<:Flag}
    error("isolatedVertices is not defined for Flag type $T")
    return missing
end

function removeIsolated(F::T) where {T<:Flag}
    isoV = isolatedVertices(F)
    return subFlag(F, .!isoV)
end

"""
    vertexColor(::T, ::Int) where {T<:Flag}

Returns the color of vertices in colored Flags. The default is the case of a vertex-transitive Flags-type, where all vertices have color `1`.
"""
function vertexColor(::T, ::Int) where {T<:Flag}
    return 1
end

"""
distinguish(F::T, v::Int, W::BitVector)::UInt where {T<:Flag}

Given a Flag `F`, a vertex `v` and a subset of vertices indicated by `W`, distinguish `v` by analyzing it's relationship to the vertices `W`. This may, for example, be the number of edges between `v` and the cell `W`, or the number of triangles with `v` and one/two vertices of `W`. The type of result does not matter, as it does get hashed after.
"""
function distinguish(F::T, v::Int, W::BitVector)::UInt where {T<:Flag}
    error("distinguish is not defined for Flag type $T")
    return missing
end

"""
    isVariableVertex(F::T, v::Int) where {T<:Flag}

Returns true if vertex `v` is one of the "variable vertices", i.e. vertices of which the number goes towards infinity. Per default, it always returns true. But, for example, for partially labeled Flags, it only returns true if the vertex is unlabeled.
"""
function isVariableVertex(F::T, v::Int) where {T<:Flag}
    return true
end

"""
    maxPredicateArguments(::Type{T}) where {T<:Flag}

Maximum number of arguments of a predicate in the theory 'T'. For instance, this is '2' for graphs, as the only predicate, the edge predicate, takes two arguments.
"""
function maxPredicateArguments(::Type{T}) where {T<:Flag}
    error("maxPredicateArguments is not defined for flag type $T")
    return missing
end

function predicateType(::Type{T}) where {T<:Flag}
    error("predicateType is not defined for flag type $T")
    return missing
end

"""
    isIsomorphic(F::T, G::T) where {T<:Flag}

Checks if two flags are isomorphic.
"""
@memoize Dict{Tuple{Flag,Flag},Bool} function isIsomorphic(F::T, G::T) where {T<:Flag}
    # Can be optimized! Do not need to run the full algorithm.
    countEdges(F) != countEdges(G) && return false
    return labelCanonically(F) == labelCanonically(G)
end

"""
    isSubFlag(F::T, G::T) where {T<:Flag}

Checks if 'F' appears as sub-flag of 'G'.
"""
function isSubFlag(F::T, G::T; induced=F isa InducedFlag) where {T<:Flag}
    # Very basic brute force algorithm
    m = size(F)
    n = size(G)
    for c in combinations(1:n, m)
        if induced
            if isIsomorphic(F, subFlag(G, c))
                return true
            end
        else
            for d in SymmetricGroup(m)
                if subFlag(G, c) == glue(F, subFlag(G, c), d.d)
                    return true
                end
            end
        end
    end
    return false
end

"""
    isAllowed(F::T) where {T<:Flag}

Sometimes one may want to create a flag-algebra with inherently forbidden flags, instead of attaching it to a model. Then one should implement (or locally overwrite) this function.
"""
function isAllowed(F::T) where {T<:Flag}
    return true
end

"""
    isAllowed(F::T, e::P) where {T<:Flag, P<:Predicate}

Sometimes one may want to create a flag-algebra with inherently forbidden flags, instead of attaching it to a model. This function should return true iff the predicate P can be set to true (i.e. the edge P can be added).
"""
function isAllowed(F::T, e) where {T<:Flag}
    return true
end

"""
    allowMultiEdges(::T) where {T<:Flag}

Can edges be added multiple times? More generally, can we repeatedly add to the same predicate value?

For most combinatoric models this should return `false`.
"""
function allowMultiEdges(::Type{T}) where {T<:Flag}
    return false
end

import Base.^
function ^(F::T, i::Int) where {T<:Flag}
    @assert i >= 0
    if i == 0
        return one(T)
    end
    return F * F^(i - 1)
end

include("InducedFlags.jl")
include("Graphs.jl")
include("ConstantWeightCodes.jl")
include("DirectedGraphs.jl")
include("EdgeColoredGraphs.jl")
include("PartiallyLabeledFlags.jl")
include("BinaryTrees.jl")
include("EdgeMarkedFlags.jl")
include("SymmetricFunctions.jl")
include("HarmonicFlags.jl")
include("ProductFlag.jl")
include("FreeVariables.jl")
include("PartiallyColoredFlags.jl")
