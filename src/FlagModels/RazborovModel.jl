export RazborovModel, computeRazborovBasis!

using SparseArrays

include("../utils/RegularRepresentation.jl")

"""
    RazborovModel{T<:Flag, N, D} <: AbstractFlagModel{T, N, D}

A (not fully symmetry reduced) Razborov-style model. If T is an InducedFlag, the hierarchy is the same as the one implemented in Flagmatic. If T is not induced, then a Moebius-transform is applied only on the labeled vertices. The resulting hierarchy is then a basis-transformation of the usual hierarchy, and returns the same bounds, but expressed in non-induced flags.
"""
mutable struct RazborovModel{T<:Flag,N,D} <: AbstractFlagModel{T,N,D}
    basis::Dict{T,Vector{PartiallyLabeledFlag{T}}}
    blockSymmetry::Dict
    sdpData::Dict{T,Dict{Union{T, String},SparseMatrixCSC{D,Int}}}
    parentModel
    quotient

    function RazborovModel{T,N,D}(parent=nothing) where {T<:Flag,N,D}
        return new(
            Dict{T,Vector{PartiallyLabeledFlag{T}}}(),
            Dict(),
            Dict{T,Dict{T,SparseMatrixCSC{D,Int}}}(),
            parent,
            Dict(),
        )
    end

    function RazborovModel{T}(parent=nothing) where {T<:Flag}
        return new{T,:limit,Int}(
            Dict{T,Vector{PartiallyLabeledFlag{T}}}(),
            Dict(),
            Dict{T,Dict{T,SparseMatrixCSC{Int,Int}}}(),
            parent,
            Dict(),
        )
    end
end

function Base.show(io::IO, m::RazborovModel{T,N,D}) where {T,N,D}
    return println(
        io,
        "Flagmatic style blocks with $(length(m.basis)) types and $(sum(length.(values(m.basis)))) flags",
    )
end

function isAllowed(m::RazborovModel{T,N,D}, F::T) where {T<:Flag,N,D}
    if m.parentModel !== nothing
        return isAllowed(m.parentModel, F)
    end
    return isAllowed(F)
end

function modelSize(m::RazborovModel)
    # return Partition([m.blockSymmetry[b].n for b in keys(m.basis)])
    return Partition(vcat([length(b) for b in values(m.basis)], [1 for _ in m.quotient]))
end

function modelBlockSizes(m::RazborovModel)
    res = Dict{Any,Int}(F => length(b) for (F, b) in m.basis)
    for (i, F) in enumerate(m.quotient)
        res["Q$i"] = -1
    end
    return res
end

function computeUnreducedRazborovBasis(
    M::RazborovModel{T,N,D}, n, maxLabels=n
) where {T<:Flag,N,D}
    razborovBasis = Dict()

    @info "Generating flags up to isomorphism..."
    flags = generateAll(T, maxLabels, [99999])
    @info "Splitting $(length(flags)) flags..."

    filter!(f -> isAllowed(M, f), flags)

    for Ftmp in flags
        for m in maxLabels:-2:size(Ftmp)
            # @show m
            k = Int((n - m) / 2)
            F = permute(Ftmp, 1:m) # add isolated vertices in labeled part
            FBlock = label(F; removeIsolated=false)[1]
            @assert size(FBlock) == m
            # @assert FBlock == label(FBlock; removeIsolated=false)[1]
            FExtended = permute(FBlock, 1:(m + k)) # add isolated vertices in unlabeled part

            preds = vcat(findUnknownPredicates(FExtended, [1:m])...)

            FMarked = EdgeMarkedFlag{PartiallyLabeledFlag{T}}(
                PartiallyLabeledFlag{T}(FExtended, m), preds
            )
            razborovBasis[FBlock] = collect(keys(moebius(FMarked).coeff))
        end
    end
    return razborovBasis
end

function computeRazborovBasis!(
    M::RazborovModel{T,N,D}, n; maxLabels=n, maxBlockSize=Inf
) where {T<:Flag,N,D}
    razborovBasis = computeUnreducedRazborovBasis(M, n, maxLabels)
    # display(razborovBasis)

    reducedBasis = Dict(mu => unique(labelCanonically.(B)) for (mu, B) in razborovBasis)
    if maxBlockSize < Inf
        filter!(x -> length(x[2]) < maxBlockSize, reducedBasis)
    end

    @info "basis reduced"
    @info "determining symmetries"
    for (mu, B) in reducedBasis
        @info "determining symmetry pattern for $mu"
        if length(B) == 1
            M.blockSymmetry[mu] = (pattern=[1;;], gen=Any[[1]], n=1)
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

        # @show muAut
        # @show length(newGen)

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
            # P[c[2], c[1]] = i
            while !isempty(newPos)
                ci = popfirst!(newPos)
                for p in newGen
                    pc = p[ci]
                    if P[pc[1], pc[2]] == 0
                        push!(newPos, pc)
                        P[pc[1], pc[2]] = i
                        # P[pc[2], pc[1]] = i
                    end
                end
            end
            i += 1
        end

        if maximum(P) > size(P, 1) # regular representation makes things worse
            @info "Regular representation not worth it for block $mu"
            symmetrize = Dict()
            ind = 1
            for i in 1:maximum(P)
                if !haskey(symmetrize, i)
                    symmetrize[i] = ind
                    c = findfirst(x -> x == i, P)
                    j = P[c[2], c[1]]
                    symmetrize[j] = ind
                    ind += 1
                end
            end
            P2 = [symmetrize[i] for i in P]
            M.blockSymmetry[mu] = (pattern=P2, gen=newGen, n=size(P, 1), fullPattern=P)
            # @info "Cannot reduce $mu from $(size(P,1)) (squared $(size(P,1)^2))to $(maximum(P)) " 
        else # regular representation makes things better
            # reg, factors = regularRepresentation(P)
            @info "Computing regular representation for block $mu"
            reg = regularRepresentation(P)
            # @show factors
            @info "Symmetrizing regular representation for block $mu"
            symmetrizedReg = Dict()
            # for (i, B) in reg
            #     @show i
            #     display(B)
            # end
            for i in 1:maximum(P)
                c = findfirst(x -> x == i, P)
                j = P[c[2], c[1]]

                ind = min(i, j)

                if !haskey(symmetrizedReg, ind)
                    # symmetrizedReg[ind] = (1 / factors[i]) * reg[i]
                    symmetrizedReg[ind] = reg[i]
                else
                    # symmetrizedReg[ind] += (1 / factors[i]) * reg[i]
                    symmetrizedReg[ind] += reg[i]
                end
            end
            # for (i, B) in symmetrizedReg
            #     @show i
            #     display(B)
            # end

            M.blockSymmetry[mu] = (
                pattern=P, gen=newGen, reg=symmetrizedReg, n=maximum(P), fullPattern=P
            )
        end
        # M.blockSymmetry[mu] = (pattern=P, gen=newGen)
    end
    @info "Block symmetries found"

    # @info "Computing regular representation, if advantageous"

    M.basis = reducedBasis
    return reducedBasis#, blockSizes
end

function computeSDP!(m::RazborovModel{T,N,D}, reservedVerts::Int) where {T,N,D}
    m.sdpData = Dict()

    for (muc, (mu, B)) in enumerate(m.basis)
        @show muc, maximum(m.blockSymmetry[mu].pattern), length(B), mu

        # mu == Hypergraph{3,5}(zeros(Bool, 0,6))

        if size(m.blockSymmetry[mu].pattern, 1) != length(B)
            @info "Basis elements were deleted, ignoring block symmetry"
            n = length(B)
            M = zeros(Int, n, n)
            ind = 1
            for i in 1:n
                for j in i:n
                    M[i, j] = ind
                    M[j, i] = ind
                    ind += 1
                end
            end
            P = (pattern=M, n=n, fullPattern=M)
        else
            P = m.blockSymmetry[mu]
        end

        maxP = maximum(P.pattern)
        for s in 1:maxP
            print("$s / $maxP      \r")
            c = findfirst(x -> x == s, P.pattern)
            if P.pattern[c[2], c[1]] < s
                continue
            end
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

            if !isInducedFlag(T) # Apply Moebius transform on labels
                if N == :limit
                    t = one(D) * glueFinite(N, T1, T2, p1Fin; labelFlags=false)
                else
                    t =
                        one(D) *
                        glueFinite(N - reservedVerts, T1, T2, p1Fin; labelFlags=false)
                end
                overlappingVerts = Int.(intersect(1:size(T2), p1Fin[1:size(T1)]))
                overlapGraph = subFlag(T2, overlappingVerts)

                missingPreds = findUnknownPredicates(overlapGraph, Vector{Int}[])
                markers = [permute(p, overlappingVerts) for p in vcat(missingPreds...)]
                tMarked = labelCanonically(
                    sum(
                        c * EdgeMarkedFlag{T}(F, markers) for (F, c) in t.coeff;
                        init=QuantumFlag{EdgeMarkedFlag{T,predicateType(T)},D}(),
                    ),
                )

                t = moebius(tMarked; label=true)
                # t = labelCanonically(t)

            else
                if N == :limit
                    # @show a
                    # @show b
                    # @show mu
                    # @show T1
                    # @show T2
                    # @show p1Fin
                    t = glueFinite(N, T1, T2, p1Fin; labelFlags=true)
                    # @show t
                else
                    t = glueFinite(N - reservedVerts, T1, T2, p1Fin; labelFlags=true)
                end
                # @show t
                # t = labelCanonically(t)
                # @show t
            end

            for (F, d) in t.coeff
                if !haskey(m.sdpData, F)
                    m.sdpData[F] = Dict()
                end
                if !haskey(m.sdpData[F], mu)
                    if haskey(P, :reg)
                        m.sdpData[F][mu] = zeros(Float64, P.n, P.n)
                    else
                        m.sdpData[F][mu] = zeros(Rational{Int}, length(B), length(B))
                    end
                end
                if haskey(P, :reg)
                    # factor = P.pattern[c[2], c[1]] == s ? 1 : 2
                    # t = P.pattern[c[2], c[1]]
                    # A = Int.(P.pattern .== s)
                    # if t != s 
                    #     A += Int.(P.pattern .== t)
                    # end
                    # m.sdpData[F][mu] .+= (norm(A) / norm(P.reg[s])) * d*P.reg[s]#*factor
                    m.sdpData[F][mu] .+= d * P.reg[s]#*factor
                else
                    m.sdpData[F][mu][P.pattern .== s] .= d
                end
            end
        end
    end

    if isInducedFlag(T)# <: InducedFlag
        # Eliminate linear dependencies 
        @info "Eliminating linear dependencies"

        Fs::Vector{T} = sort(collect(keys(m.sdpData)); by=size)
        n = maximum(size.(keys(m.sdpData)))
        union!(Fs, generateAll(T, n, [99999]))

        # expandedFs = T[]
        # for F in Fs
        #     for m in size(F):n
        #         push!(expandedFs, labelCanonically(permute(F, 1:m)))
        #     end
        # end

        # reduction = quotient(expandedFs, x -> isAllowed(m.parentModel, x))
        reduction = quotient(Fs, x -> isAllowed(m.parentModel, x))

        display(reduction)

        m.quotient = reduction

        for (i, F) in enumerate(m.quotient)
            for (G,c) in F.coeff
                if !haskey(m.sdpData, G)
                    m.sdpData[G] = Dict() 
                end
                m.sdpData[G]["Q$i"] = D[c;;]
            end
        end

        # for i in size(reduction, 1):-1:1
        #     j = findlast(x -> !iszero(x), reduction[i, :])
        #     @assert reduction[i, j] == 1
        #     F = Fs[j]
        #     quotient = sum(-reduction[i, k] * Fs[k] for k in 1:(j - 1) if reduction[i,k] != 0)
        #     m.quotient[F] = quotient
        #     @show F 
        #     @show quotient
        #     # quotient = labelCanonically(eliminateIsolated(F))
        #     # FNoIsolated = labelCanonically(subFlag(F, (1:size(F))[.!v]))

        #     # @assert quotient.coeff[FNoIsolated] == 1

        #     for (G, c) in quotient.coeff
        #         if !haskey(m.sdpData, G)
        #             m.sdpData[G] = Dict()
        #         end
        #         for (mu, b) in m.sdpData[F]
        #             if !haskey(m.sdpData[G], mu)
        #                 m.sdpData[G][mu] = zeros(
        #                     Rational{Int}, length(m.basis[mu]), length(m.basis[mu])
        #                 )
        #             end
        #             m.sdpData[G][mu] += c * b
        #         end
        #     end
        #     @info "deleting $F"
        #     delete!(m.sdpData, F)
        # end

        # total = length(m.sdpData)
        # i = 1
        # for (F, B) in m.sdpData
        #     @show i, total
        #     @show F
        #     i += 1
        #     if isAllowed(m, F)
        #         v = isolatedVertices(F)
        #         if !any(v)
        #             continue
        #         end

        #         quotient = labelCanonically(eliminateIsolated(F))
        #         FNoIsolated = labelCanonically(subFlag(F, (1:size(F))[.!v]))

        #         @assert quotient.coeff[FNoIsolated] == 1

        #         for (G, c) in quotient.coeff
        #             if !haskey(m.sdpData, G)
        #                 m.sdpData[G] = Dict()
        #             end
        #             for (mu, b) in m.sdpData[F]
        #                 if !haskey(m.sdpData[G], mu)
        #                     m.sdpData[G][mu] = zeros(
        #                         Rational{Int}, length(m.basis[mu]), length(m.basis[mu])
        #                     )
        #                 end
        #                 m.sdpData[G][mu] += c * b
        #             end
        #         end
        #     end
        #     delete!(m.sdpData, F)
        # end
    end

    @info "Razborov computation done"

    return m.sdpData
end

function buildJuMPModel(m::RazborovModel, replaceBlocks=Dict(), jumpModel=Model())
    # @show m
    # @show modelSize(m)
    b = modelBlockSizes(m)
    Y = Dict()
    constraints = Dict()

    for (mu, n) in b
        if n > 0
            P = m.blockSymmetry[mu].pattern
            name = "y[$mu]"
            # t = maximum(P)
            t = m.blockSymmetry[mu].n
            if haskey(m.blockSymmetry[mu], :reg)
                reg = m.blockSymmetry[mu].reg
                y = @variable(jumpModel, [keys(reg)], base_name = name)
                AT = typeof(1 * y[1])

                # Y[mu] = zeros(AT, t, t)
                # for s in keys(reg)
                #     Y[mu] .+= reg[s]*y[s]
                # end
                Y[mu] = sum(reg[s] * y[s] for s in keys(reg))
                if size(P, 1) > 1
                    constraints[name] = @constraint(jumpModel, Y[mu] in PSDCone())
                else
                    constraints[name] = @constraint(jumpModel, Y[mu] .>= 0)
                end
            else
                # numVars = maximum(P)
                # y = @variable(jumpModel, [1:numVars], base_name = name)
                # AT = typeof(1 * y[1])

                # Y[mu] = zeros(AT, t, t)
                # # Y[mu] = zeros(AT, size(P))
                # for s in 1:numVars
                #     Y[mu][P .== s] .+= y[s]
                # end

                # Y[mu] = sum((P .== s) * y[s] for s in 1:numVars)
                # # Y[mu] = @variable(jumpModel, [1:size(P,1),1:size(P,1)], PSD)
                # if size(P, 1) > 1
                #     constraints[name] = @constraint(jumpModel, Y[mu] in PSDCone())
                # else
                #     constraints[name] = @constraint(jumpModel, Y[mu] .>= 0)
                # end

                Y[mu] = get(replaceBlocks, mu) do
                    name = "Y$mu"
                    if n > 1
                        v = @variable(jumpModel, [1:n, 1:n], Symmetric, base_name = name)
                        constraints[name] = @constraint(jumpModel, v in PSDCone())
                        return v
                    else
                        v = @variable(jumpModel, [1:1, 1:1], Symmetric, base_name = name)
                        constraints[name] = @constraint(jumpModel, v .>= 0)
                        return v
                    end
                end
            end
        else
            y = @variable(jumpModel, [1:1,1:1], base_name = mu)
            Y[mu] = y
            # i = parse(Int,mu[2:end])
            # for (G, c) in m.quotient[i].coeff
            #     graphCoefficients[G] = get(graphCoefficients, G, 0 * c * y) + c * y
            # end
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

    return (model=jumpModel, variables=graphCoefficients, blocks=Y, constraints=constraints)
end

function computeUnreducedRazborovBasis(
    M::RazborovModel{BinaryTreeFlag,N,D}, n, maxLabels=n
) where {N,D}
    razborovBasis = Dict()

    # @info "Generating flags up to isomorphism..."
    # flags = generateAll(BinaryTreeFlag, maxLabels, [99999])
    # @info "Splitting $(length(flags)) flags..."

    # filter!(f -> isAllowed(M, f), flags)

    # for Ftmp in flags
    #     for m in maxLabels:-2:size(Ftmp)
    #         k = Int((n - m) / 2)
    #         F = permute(Ftmp, 1:m) # add isolated vertices in labeled part
    #         FBlock = label(F; removeIsolated=false)[1]
    #         @assert FBlock == label(FBlock; removeIsolated=false)[1]
    #         FExtended = permute(FBlock, 1:(m + k)) # add isolated vertices in unlabeled part

    #         preds = vcat(findUnknownPredicates(FExtended, [1:m])...)

    #         FMarked = EdgeMarkedFlag{PartiallyLabeledFlag{T}}(
    #             PartiallyLabeledFlag{T}(FExtended, m), preds
    #         )
    #         razborovBasis[FBlock] = collect(keys(moebius(FMarked).coeff))
    #     end
    # end
    # razborovBasis

    razborovBasis = Dict()
    trees = generateAll(BinaryTree, n, [1]; upToIso=true)
    for T in trees
        m = size(T) # = n + (n-k)/2
        # @show k = 3*n-2*m

        # k + 2(m-k) <= n
        # 2m - k <= n 
        # 2m - n <= k
        # @show T 
        # @show max((2*m-n),0):m
        # @show n

        # if m % 2 != n % 2
        #     continue 
        # end

        for k in n:-2:max((2 * m - n), 0)
            # @show k

            # Only maximum number of unlabeled leaves
            if n != k + 2 * (m - k)
                continue
            end

            for c in combinations(1:m, k)
                # @show c
                tLabeled = subFlag(T, c)

                tCanLabeled, tCanLabelPerm = labelPerm(tLabeled)
                tCanLabeled = BinaryTreeFlag(tCanLabeled)

                auts = aut(tCanLabeled)
                fullGroup = generateGroup(perm.(auts.gen), auts.size)

                if auts.size == 1
                    fullGroup = [AbstractAlgebra.perm(1:k)]
                end

                if true#k == 0
                    # @show auts
                    # @show fullGroup
                end

                for p in fullGroup
                    # if !haskey(razborovBasis, (tCanLabeled, k))
                    #     razborovBasis[(tCanLabeled, k)] = Set([])
                    # end
                    if !haskey(razborovBasis, tCanLabeled)
                        razborovBasis[tCanLabeled] = Set([])
                    end

                    # @show tCanLabelPerm
                    tCanLabelPermInv = [
                        findfirst(x -> x == i, tCanLabelPerm) for
                        i in 1:length(tCanLabelPerm)
                    ]

                    q = collect(1:m)
                    q[c] .= 1:k
                    q[setdiff(1:m, c)] .= (k + 1):m
                    # @show k
                    q[c] .= p.d[tCanLabelPermInv[1:k]]

                    # @error "DO NOT INVERT? ADD CHECK"

                    # @show subFlag(T, c)
                    # @show tCanLabeled
                    # @assert subFlag(T, q[c]) == tCanLabeled

                    push!(
                        razborovBasis[tCanLabeled],
                        # razborovBasis[(tCanLabeled, k)],
                        PartiallyLabeledFlag{BinaryTreeFlag}(BinaryTreeFlag(T, q), k),
                    )

                    # @assert PartiallyLabeledFlag{BinaryTreeFlag}(BinaryTreeFlag(T, q), k) == labelCanonically(PartiallyLabeledFlag{BinaryTreeFlag}(BinaryTreeFlag(T, q), k)) "A = $(PartiallyLabeledFlag{BinaryTreeFlag}(BinaryTreeFlag(T, q), k)), B = $(labelCanonically(PartiallyLabeledFlag{BinaryTreeFlag}(BinaryTreeFlag(T, q), k)) )"

                    # if (tCanLabeled, k) == Test 
                    #     @show  T 
                    #     @show k 
                    #     @show c 
                    #     @show tCanLabeled
                    #     @show p
                    #     @show PartiallyLabeledFlag{BinaryTreeFlag}( BinaryTreeFlag(T, q), k)
                    # end
                end
            end
        end
    end
    @show keys(razborovBasis)
    return razborovBasis
end

function roundResults(
    m::RazborovModel{T,N,D}, jumpModel, variables, blocks, constraints; prec=1e-5
) where {T,N,D}
    ex = Dict()

    den = round(BigInt, 1 / prec)
    function roundDen(x)
        return round(BigInt, den * x)//den
    end

    for (mu, b) in blocks
        if mu isa String
            # ex[mu] = rationalize(BigInt, value(b); tol=prec)#; digits = digits)
            ex[mu] = roundDen(value(b))
        else
            ex[mu] = roundRationalPSD(value(b); baseType=BigInt, prec=prec)
        end
    end

    return ex
end

function verifySOS(m::RazborovModel, sol::Dict; io::IO=stdout)
    if io !== nothing
        println(io, "Flagmatic model")

        for mu in keys(sol)
            if mu isa String
                continue
            end

            println(io, "\nBlock of type $mu with flags:")
            println.(io, m.basis[mu])

            println(io, "PSD matrix:")
            psd = sol[mu] isa Matrix ? sol[mu] : sol[mu].psd
            show(io, "text/plain", psd)
            println(io)
            if !(sol[mu] isa Matrix) && size(sol[mu].psd, 1) > 1
                println(io, "With Cholesky factorization:")
                show(io, "text/plain", sol[mu].chol)
                println(io)
            end

            println(io, "Nonzero flag products:")
            n = size(m.basis[mu], 1)
            # @show mu
            # @show sol[mu]
            psd = sol[mu] isa Matrix ? sol[mu] : sol[mu].psd
            for i in 1:n
                for j in i:n
                    if !iszero(psd[i, j])
                        tmp = sum(m.sdpData) do (G, B)
                            if haskey(B, mu)
                                return Rational{BigInt}(B[mu][i, j]) * G
                            else
                                return BigInt(0)//1 * G
                            end
                        end
                        print(
                            io,
                            "Product at $((i,j)) is $(psd[i,j]) ⋅ $(m.basis[mu][i]) ⋅ $(m.basis[mu][j]) ",
                        )
                        # println(io, "$(psd[i,j]) ⋅ ($tmp)")
                        println(io, "=$(Rational{BigInt}(psd[i,j])*tmp)")
                    end
                end
            end
            println(io, "Block $mu total:")
            println(
                io,
                "$(sum(m.sdpData) do (G, B)
             if haskey(B, mu)
                 return dot(B[mu], psd) * G
             else
                 return BigInt(0) // 1 * G
             end
         end)>=0",
            )
        end

        if length(m.quotient) > 0
            println(io, "Quotient:")
            for (i, c) in enumerate(m.quotient)
                if haskey(sol, "Q$i") && !iszero(sol["Q$i"])
                    print(io, "$(sol["Q$i"]) ⋅ ($c) ")
                    println(io, "=$(Rational{BigInt}(sol["Q$i"])*c)= 0")
                end
            end
            println(io, "Quotient sum:")
            println(
                io,
                "$(sum(enumerate(m.quotient)) do (i, F)
        Rational{BigInt}(get(sol, "Q$i", 0 // 1)) * F
    end)=0",
            )
        end
    end

    res = sum(m.sdpData) do (G, B)
        if mu isa String 
            return BigInt(0)//1
        end
        sum(B) do (mu, b)
            if haskey(sol, mu)
                psd = sol[mu] isa Matrix ? sol[mu] : sol[mu].psd
                return dot(Rational{BigInt}.(psd), b) * G
            else
                return BigInt(0)//1 * G
            end
        end
    end

    res += sum(enumerate(m.quotient)) do (i, F)
        Rational{BigInt}(get(sol, "Q$i", 0//1)) * F
    end

    if io !== nothing
        println(io, "\nRazborov model result:")
        println(io, "$(res)>= 0")
        println(io)
    end

    return res
end
