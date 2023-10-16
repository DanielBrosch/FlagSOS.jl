export RazborovModel, computeRazborovBasis!

"""
    RazborovModel{T<:Flag, N, D} <: AbstractFlagModel{T, N, D}

A (not fully symmetry reduced) Razborov-style model. If T is an InducedFlag, the hierarchy is the same as the one implemented in Flagmatic. If T is not induced, then a Moebius-transform is applied only on the labeled vertices. The resulting hierarchy is then a basis-transformation of the usual hierarchy, and returns the same bounds, but expressed in non-induced flags.
"""
mutable struct RazborovModel{T<:Flag,N,D} <: AbstractFlagModel{T,N,D}
    basis::Dict{T,Vector{PartiallyLabeledFlag{T}}}
    blockSymmetry::Dict
    sdpData::Dict{T,Dict{T,SparseMatrixCSC{D,Int}}}
    parentModel

    function RazborovModel{T,N,D}(parent=nothing) where {T<:Flag,N,D}
        return new(
            Dict{T,Vector{PartiallyLabeledFlag{T}}}(),
            Dict(),
            Dict{T,Dict{T,SparseMatrixCSC{D,Int}}}(),
            parent,
        )
    end

    function RazborovModel{T}(parent=nothing) where {T<:Flag}
        return new{T,:limit,Int}(
            Dict{T,Vector{PartiallyLabeledFlag{T}}}(),
            Dict(),
            Dict{T,Dict{T,SparseMatrixCSC{Int,Int}}}(),
            parent,
        )
    end
end

function isAllowed(m::RazborovModel{T,N,D}, F::T) where {T<:Flag,N,D}
    if m.parentModel !== nothing
        return isAllowed(m.parentModel, F)
    end
    return isAllowed(F)
end

function modelSize(m::RazborovModel)
    return Partition([length(b) for b in values(m.basis)])
end

function modelBlockSizes(m::RazborovModel)
    return Dict(F => length(b) for (F, b) in m.basis)
end

function computeRazborovBasis!(M::RazborovModel{T,N,D}, n) where {T<:Flag,N,D}
    razborovBasis = Dict()

    @info "Generating flags up to isomorphism..."
    flags = generateAll(T, n, [99999])
    @info "Splitting $(length(flags)) flags..."

    filter!(f -> isAllowed(M, f), flags)

    for Ftmp in flags
        for m in n:-2:size(Ftmp)
            k = Int((n - m) / 2)
            F = permute(Ftmp, 1:m) # add isolated vertices in labeled part
            FBlock = label(F; removeIsolated=false)[1]
            @assert FBlock == label(FBlock; removeIsolated=false)[1]
            FExtended = permute(FBlock, 1:(m + k)) # add isolated vertices in unlabeled part

            preds = vcat(findUnknownPredicates(FExtended, [1:m])...)

            FMarked = EdgeMarkedFlag{PartiallyLabeledFlag{T}}(
                PartiallyLabeledFlag{T}(FExtended, m), preds
            )
            razborovBasis[FBlock] = collect(keys(moebius(FMarked).coeff))
        end
    end

    @info "determining symmetries"

    reducedBasis = Dict(mu => unique(labelCanonically.(B)) for (mu, B) in razborovBasis)

    @info "basis reduced"
    for (mu, B) in reducedBasis

        if length(B) == 1
            M.blockSymmetry[mu] = (pattern=[1;;], gen=Any[[1]])
            continue
        end

        muAut = aut(mu)

        newGen = []
        for p in muAut.gen
            gen = zeros(Int, length(B))
            for (i, b) in enumerate(B)
                @assert length(p) == b.n
                pb = labelCanonically(
                    PartiallyLabeledFlag{T}(
                        permute(b.F, vcat(p, (length(p) + 1):size(b))), b.n
                    ),
                )
                gen[i] = findfirst(x -> x == pb, B)
            end
            push!(newGen, gen)
        end

        P = zeros(Int, length(B), length(B))
        i = 1
        c = [1, 1]
        while true
            pos = findnext(x -> x == 0, P, CartesianIndex{2}(c...))
            pos === nothing && break
            c[1] = pos[1]
            c[2] = pos[2]
            newPos = [c]
            P[c[1], c[2]] = i
            P[c[2], c[1]] = i
            while !isempty(newPos)
                ci = popfirst!(newPos)
                for p in newGen
                    pc = p[ci]
                    if P[pc[1], pc[2]] == 0
                        push!(newPos, pc)
                        P[pc[1], pc[2]] = i
                        P[pc[2], pc[1]] = i
                    end
                end
            end
            i += 1
        end

        M.blockSymmetry[mu] = (pattern=P, gen=newGen)
    end
    @info "Block symmetries found"

    M.basis = reducedBasis
    return reducedBasis#, blockSizes
end

function computeSDP!(m::RazborovModel{T,N,D}) where {T,N,D}
    m.sdpData = Dict()

    for (muc, (mu, B)) in enumerate(m.basis)
        @show muc, maximum(m.blockSymmetry[mu].pattern), length(B), mu

        # mu == Hypergraph{3,5}(zeros(Bool, 0,6))

        P = m.blockSymmetry[mu]
        maxP = maximum(P.pattern)
        for s in 1:maxP
            print("$s / $maxP      \r")
            c = findfirst(x -> x == s, P.pattern)
            i = c[1]
            j = c[2]
            a = B[i]
            b = B[j]

            n1 = size(a)
            n2 = size(b)
            k = a.n

            newSize = k + (n1 - k) + (n2 - k)
            p = collect(1:newSize)
            p[(k + 1):n1] = (n2 + 1):newSize

            T1 = a.F
            p1 = p[1:size(a.F)]
            p1 = vcat(p1, setdiff(1:newSize, p1))

            T2 = b.F
            p2 = 1:size(b.F)

            p2Inv = [findfirst(x -> x == i, p2) for i in 1:n2]
            p2Inv = vcat(p2Inv, setdiff(1:newSize, p2Inv))
            p1Fin = p2Inv[p1]
            p1Fin = vcat(p1Fin, setdiff(1:newSize, p1Fin))

            @views sort!(p1Fin[(n1 + 1):end])

            p1Fin = Int.(p1Fin)

            if !(T <: InducedFlag) # Apply Moebius transform on labels
                t = one(D) * glueFinite(N, T1, T2, p1Fin; labelFlags=false)
                overlappingVerts = Int.(intersect(1:size(T2), p1Fin[1:size(T1)]))
                overlapGraph = subFlag(T2, overlappingVerts)

                missingPreds = findUnknownPredicates(overlapGraph, Vector{Int}[])
                markers = [permute(p, overlappingVerts) for p in vcat(missingPreds...)]
                tMarked = labelCanonically(
                    sum(
                        c * EdgeMarkedFlag{T}(F, markers) for (F, c) in t.coeff;
                        init=QuantumFlag{EdgeMarkedFlag{T, predicateType(T)},D}(),
                    ),
                )

                t = moebius(tMarked)
                t = labelCanonically(t)

            else
                t = glueFinite(N, T1, T2, p1Fin; labelFlags=false)
                t = labelCanonically(t)
            end

            for (F, c) in t.coeff
                if !haskey(m.sdpData, F)
                    m.sdpData[F] = Dict()
                end
                if !haskey(m.sdpData[F], mu)
                    m.sdpData[F][mu] = zeros(Rational{Int}, length(B), length(B))
                end
                m.sdpData[F][mu][P.pattern .== s] .= c
            end
        end
    end

    if T <: InducedFlag
        # Eliminate linear dependencies 
        @info "Eliminating linear dependencies"

        for (F, B) in m.sdpData
            if isAllowed(m, F)
                v = isolatedVertices(F)
                if !any(v)
                    continue
                end

                substitution = eliminateIsolated(F)
                FNoIsolated = labelCanonically(subFlag(F, (1:size(F))[.!v]))

                @assert substitution.coeff[FNoIsolated] == 1

                for (G, c) in substitution.coeff
                    if !haskey(m.sdpData, G)
                        m.sdpData[G] = Dict()
                    end
                    for (mu, b) in m.sdpData[F]
                        if !haskey(m.sdpData[G], mu)
                            m.sdpData[G][mu] = zeros(
                                Rational{Int}, length(m.basis[mu]), length(m.basis[mu])
                            )
                        end
                        m.sdpData[G][mu] += c * b
                    end
                end
            end
            delete!(m.sdpData, F)
        end
    end

    return m.sdpData
end

function buildJuMPModel(m::RazborovModel, replaceBlocks=Dict(), jumpModel=Model())
    b = modelBlockSizes(m)
    Y = Dict()

    for (mu, n) in b
        P = m.blockSymmetry[mu].pattern
        name = "y[$mu]"
        t = maximum(P)
        y = @variable(jumpModel, [1:t], base_name = name)
        AT = typeof(1 * y[1])
        Y[mu] = zeros(AT, size(P))
        for s in 1:t
            Y[mu][P .== s] .+= y[s]
        end
        if size(P, 1) > 1
            @constraint(jumpModel, Y[mu] in PSDCone())
        else
            @constraint(jumpModel, Y[mu] .>= 0)
        end
    end

    graphCoefficients = Dict()

    for G in keys(m.sdpData)
        AT = typeof(sum(collect(values(Y))[1]))
        eG = AT()
        for mu in keys(b)
            if haskey(m.sdpData[G], mu)
                for (i, j, c) in Iterators.zip(findnz(m.sdpData[G][mu])...)
                    i > j && continue
                    fact = (i == j ? 1 : 2)
                    add_to_expression!(eG, fact * c, Y[mu][i, j])
                end
            end
        end
        graphCoefficients[G] = eG
    end

    return (model=jumpModel, variables=graphCoefficients, blocks=Y, constraints=[])
end
