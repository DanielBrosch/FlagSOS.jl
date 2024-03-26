export addFlag!, LasserreModel

include("../utils/PermutationModuleQuotients.jl")

using SparseArrays: SparseMatrixCSC, spzeros, findnz

# Describes a basis for a single graph indexing the SDP. I.e. a basis of the (symmetry reduced) ways to label a graph.
struct FlagSymmetries{T<:Flag}
    F::T
    shape::Vector{Vector{Int}}
    consideredVecs::Vector{Int}
    rowAut::Any

    function FlagSymmetries(F::T) where {T<:Flag}
        cV = [i for i in 1:size(F) if isVariableVertex(F, i)]

        function determineShape(g::T) where {T<:Flag}
            nV = size(g)
            shape = Vector{Vector{Int64}}([])
            covered = []
            for i in cV
                if !(i in covered)
                    part = [i]
                    for j in setdiff((i+1):nV, covered)
                        if isSym(g, i, j)
                            push!(part, j)
                            push!(covered, j)
                        end
                    end
                    push!(shape, sort!(part))
                    push!(covered, i)
                end
            end
            sort!(shape; by=length, rev=true)
            return shape
        end

        function reduceAutomorphismsToRows(automs, shape)
            if length(shape) == 0
                return automs
            end

            res = []
            for p in automs
                s2 = [sort!([p[i] for i in part]) for part in shape]
                p2 = [findfirst(x -> x == s2[i], shape) for i in 1:length(shape)]
                push!(res, p2)
            end
            return setdiff(unique!(res), [collect(1:length(shape))])
        end
        @show F 
        shape = determineShape(F)
        @show shape
        automs = aut(F)
        @show automs
        ge = reduceAutomorphismsToRows(automs.gen, shape)
        @show ge
        s = Integer(automs.size / prod([factorial(length(s)) for s in shape]))
        rowAut = (gen=ge, size=s, fullGroup=generateGroup(perm.(ge), s))

        return new{T}(F, shape, cV, rowAut)
    end
end

struct SpechtFlag{T<:Flag}
    F::FlagSymmetries{T}
    T::AbstractAlgebra.Generic.YoungTableau{Int}
    freePos::Int
end

"""
    LasserreModel{T<:Flag, N, D} <: AbstractFlagModel{T, N, D}

A fully symmetry reduced Lasserre-style model.
"""
mutable struct LasserreModel{T<:Flag,N,D} <: AbstractFlagModel{T,N,D}
    generators::Vector{FlagSymmetries{T}}
    basis::Dict{AbstractAlgebra.Generic.Partition,Vector{SpechtFlag{T}}}
    sdpData::Dict{T,Dict{AbstractAlgebra.Generic.Partition,SparseMatrixCSC{D,Int}}}
    parentModel

    function LasserreModel{T,N,D}(parent=nothing) where {T<:Flag,N,D}
        return new(
            FlagSymmetries{T}[],
            Dict{AbstractAlgebra.Generic.Partition,Vector{SpechtFlag{T}}}(),
            Dict{T,Dict{AbstractAlgebra.Generic.Partition,SparseMatrixCSC{D,Int}}}(),
            parent,
        )
    end

    function LasserreModel{T}(parent=nothing) where {T<:Flag}
        return new{T,:limit,Int}(
            FlagSymmetries{T}[],
            Dict{AbstractAlgebra.Generic.Partition,Vector{SpechtFlag{T}}}(),
            Dict{T,Dict{AbstractAlgebra.Generic.Partition,SparseMatrixCSC{Int,Int}}}(),
            parent,
        )
    end
end

function modelSize(m::LasserreModel)
    return Partition([length(b) for b in values(m.basis)])
end

function modelBlockSizes(m::LasserreModel)
    return Dict(mu => length(b) for (mu, b) in m.basis)
end

function findColSpanningSetV3(A)
    F = qr(A, Val(true))
    r = sum(abs.(diag(F.R)) .> 0.00000001)

    if r == 0
        return []
    end

    return sort(F.p[1:r])
end

function addFlag!(
    m::LasserreModel{T,N,D},
    g::U;
    allowedNumberOfLabels=0:size(g),
    maxOutVertices=2 * size(g),
) where {T<:Flag,N,D,U<:Flag}
    @show g
    g = labelCanonically(g)
    gS = FlagSymmetries(g)
    @show gS
    if gS in m.generators
        return nothing
    end

    push!(m.generators, gS)

    # Decomposing the quotient
    graphSize = size(g)
    n = N == :limit ? 2 * graphSize : N
    lambda = nothing

    freePos = 1

    if graphSize > 0
        @assert n - graphSize > 0
        lambda = AbstractAlgebra.Partition(
            vcat([n - graphSize], [length(p) for p in gS.shape])
        )

        if n - graphSize < lambda.part[1]
            # if n-graphSize < length(gS.shape[1])
            freePos = findfirst(x -> x == n - graphSize, lambda.part)
        end
    else
        lambda = AbstractAlgebra.Partition([1])
    end

    info = []
    #TODO: Update to use decomposeModule
    for mu in biggerShapes(lambda)
        #TODO: check if congruent % 2 is enough (yes according to Flagmatic paper)
        if freePos != 1 || (sum(mu.part[2:end]) in allowedNumberOfLabels &&
                            sum(mu.part[2:end]) + 2 * (size(g) - sum(mu.part[2:end])) <= maxOutVertices) #&& sum(mu.part[2:end]) + (length(mu.part) > 1 ? mu.part[2] : 0) + 2*(m.flagType.nV(g) - sum(mu.part[2:end])) <= maxOutVertices # maxLabelled #&& sum(mu.part[2:end]) % 2 == maxLabelled % 2
            K = Kostka(mu, lambda)

            reynolds = zeros(Int64, K[1], K[1])
            if gS.rowAut.size > 1
                generator = []
                for p in gS.rowAut.gen
                    # @show K 
                    # @show p
                    # @show shiftElement(p)
                    # @show insertElement(p, freePos)
                    # @assert insertElement(p, freePos)[freePos] == freePos
                    # if freePos == 1
                    #     @assert shiftElement(p) == insertElement(p, freePos)
                    # end
                    # push!(generator, (p, semiTabPermMat(K, shiftElement(p))))
                    push!(generator, (p, semiTabPermMat(K, insertElement(p, freePos))))
                end
                fullGroup = generateGroup(generator, gS.rowAut.size, true)
                for p in fullGroup[1]
                    reynolds += fullGroup[2][p]
                end
            else
                for i in 1:K[1]
                    reynolds[i, i] = 1
                end
            end

            push!(info, (mu=mu, R=reynolds, basis=[], K=K))

            colSet = findColSpanningSetV3(reynolds)

            if length(colSet) > 0
                muInd = Partition(mu[2:end])
                if !haskey(m.basis, muInd)
                    m.basis[muInd] = []
                end
                for t in K[2][colSet]
                    push!(m.basis[muInd], SpechtFlag{U}(gS, t, freePos))
                    push!(info[end].basis, SpechtFlag{U}(gS, t, freePos))
                end
            end
        end
    end
    return info
end

#TODO: Replace with optimized code from crossing project!
function multiplyPolytabsAndSymmetrize(
    m::LasserreModel{T,N,D},
    sp1::SpechtFlag{U},
    sp2::SpechtFlag{U},
    maxVert=-1,
    # limit=true,
    splitByOverlaps=false,
    useGroups=false,
    reservedVerts=0
) where {T<:Flag,N,D,U<:Flag}
    # @assert sum(length.(sp1.F.shape)) == size(sp1.F.F)
    limit = N == :limit
    # if !limit 
    #     N -= reservedVerts
    # end

    fixVerts1 = setdiff(1:size(sp1.F.F), sp1.F.consideredVecs)
    fixVerts2 = setdiff(1:size(sp2.F.F), sp2.F.consideredVecs)

    @assert fixVerts1 == fixVerts2

    shape1 = sp1.F.shape
    shape2 = sp2.F.shape

    if length(shape1) == 0
        shape1 = [[]]
    end
    if length(shape2) == 0
        shape2 = [[]]
    end
    grp1 = sp1.F.rowAut.fullGroup
    grp2 = sp2.F.rowAut.fullGroup

    # IntOrPoly = Union{Int, Polynomial{Int,Int,1}}
    # n = limit ? sum(p1.part) : (fixedN > -1 ? fixedN : Polynomial([[1] => 1]))
    # la = vcat([n - sum(p1.part[2:end])], p1.part[2:end])
    removedVerts = 0
    if !limit # same number of labels in partially labeled flag algebra
        @assert size(sp1.F.F) - sum(length.(sp1.F.shape)) == size(sp2.F.F) - sum(length.(sp2.F.shape))
        removedVerts = size(sp1.F.F) - sum(length.(sp1.F.shape))
    end


    # @show reservedVerts
    # @show removedVerts

    n = limit ? sum(sp1.T.part) : (N > -1 ? N - reservedVerts - removedVerts : Polynomials.Polynomial([0, 1]) - removedVerts)
    la = vcat([n - sum(sp1.T.part[2:end])], sp1.T.part[2:end])
    # la = deepcopy(sp1.T.part.part)
    # la[sp1.freePos] += n - sum(sp1.T.part)
    # @show sp1 
    # @show sp1.freePos
    # @show sp1.T
    # @show sp1.T.part
    # @show n 

    if sp1.freePos !== 1
        @assert sum(sp1.T.part) == n
    end
    if sp2.freePos !== 1
        @assert sum(sp2.T.part) == n
    end

    # la = vcat(sp1.T.part[1:sp1.freePos-1], n - sum(sp1.T.part) + sp1.T.part[sp1.freePos], sp1.T.part[sp1.freePos+1:end])
    # @show la 



    (newVariant, fact) = symPolytabloidProduct(sp1.T, sp2.T, la, limit)

    combinedOverlaps = Dict([])
    for (a, b) in newVariant
        # cord = [2:size(a, 1)..., 1]
        # shiftedMat = a[cord, cord]
        # shiftedMat[end, end] = 0
        # if sp1.freePos != sp2.freePos
        #     @show sp1.freePos
        #     @show sp2.freePos
        # end
        # cord = [2:size(a, 1)..., 1]

        coord1 = [setdiff(1:size(a, 2), [sp1.freePos])..., sp1.freePos]
        coord2 = [setdiff(1:size(a, 1), [sp2.freePos])..., sp2.freePos]
        shiftedMat = a[coord2, coord1]

        # coord1 = [setdiff(1:size(a,1), [sp1.freePos])..., sp1.freePos]
        # coord2 = [setdiff(1:size(a,2), [sp2.freePos])..., sp2.freePos]
        # shiftedMat = a[coord1, coord2]

        shiftedMat[end, end] = 0

        # naive
        # if maxVert == -1 || sum(shiftedMat) <= maxVert

        # Flagmatic style
        # if maxVert == -1 ||
        #     sum(shiftedMat[1:(end - 1), 1:(end - 1)]) +
        #    2 * max(sum(shiftedMat[:, end]), sum(shiftedMat[end, :])) <= maxVert
        #     combinedOverlaps[Int64.(shiftedMat)'] = b//fact
        # end
        combinedOverlaps[Int64.(shiftedMat)'] = b // fact
    end

    # reduce using automorphisms
    combinedOverlapsReduced = Dict{Any,D}([])
    if useGroups
        @assert limit "TODO: Fix finite case with group speedup"
        #TODO Current solution does reduce it somewhat, but not fully?
        for B in keys(combinedOverlaps)

            # new version
            # if false
            #     B1s = unique([B[:,vcat(p.d,length(p.d)+1:size(B,2))] for p in vcat(grp1,[(d=collect(1:size(B,2)),)]) ])
            #     minB2 = reshape(minimum([vec(C[vcat(q.d,length(q.d)+1:size(B,1)),:]) for q in vcat(grp2,[(d=collect(1:size(B,1)),)]) for C in B1s]),size(B))
            # else #old version
            #     cols = [B[:,i] for i = 1:size(B,2)]
            #     colOrder = sort(unique(cols))
            #     cols = [findfirst(x->x==bi,colOrder) for bi in cols]
            #     minCol = length(grp1) > 0 ? cols[1:length(grp1[1].d)] : cols
            #     minp = collect(1:size(B,2))
            #     for p in grp1
            #         if cols[p.d] < minCol
            #             minCol = cols[p.d]
            #             minp = p.d
            #         end
            #     end
            #     minB1 = B[:,vcat(minp,length(minp)+1:size(B,2))]
            #     rows = [minB1[i,:] for i = 1:size(B,1)]
            #     rowOrder = sort(unique(rows))
            #     rows = [findfirst(x->x==bi,rowOrder) for bi in rows]
            #     minRow = length(grp2) > 0 ? rows[1:length(grp2[1].d)] : rows
            #     minp = collect(1:size(B,1))

            #     for p in grp2
            #         if rows[p.d] < minRow
            #             minRow = rows[p.d]
            #             minp = p.d
            #         end
            #     end

            #     minB2 = minB1[vcat(minp,length(minp)+1:size(B,1)),:]
            # end
            minB2 = reshape(
                minimum([
                    vec(
                        B[
                            vcat(q.d, (length(q.d)+1):size(B, 1)),
                            vcat(p.d, (length(p.d)+1):size(B, 2)),
                        ],
                    ) for p in vcat(grp1, [(d=collect(1:size(B, 2)),)]) for
                    q in vcat(grp2, [(d=collect(1:size(B, 1)),)])
                ]),
                size(B),
            )
            combinedOverlapsReduced[minB2] =
                combinedOverlaps[B] + get!(combinedOverlapsReduced, minB2, 0)
        end
    else
        combinedOverlapsReduced = combinedOverlaps
    end

    resUnsorted = Dict{T,D}([])

    # overlap matrices to graphs
    for B in keys(combinedOverlapsReduced)
        p = zeros(Int64, sum(B) + length(fixVerts1))
        for i in fixVerts1
            p[i] = i
        end
        vecShape1 = vcat(shape1...)
        if length(vecShape1) < sum(B)#length(p)
            vecShape1 = vcat(vecShape1, setdiff(1:length(p), vecShape1, fixVerts1))
        end

        vecShape2 = vcat(shape2...)
        if length(vecShape2) < sum(B)#length(p)
            vecShape2 = vcat(vecShape2, setdiff(1:length(p), vecShape2, fixVerts2))
        end

        # @show vecShape2

        correspondingEntries = Matrix{Vector{Int64}}([
            Int64[] for i in 1:size(B)[1], j in 1:size(B)[2]
        ])

        cur = 1
        for i in 1:size(B, 1)
            for j in 1:size(B, 2)
                if B[i, j] > 0
                    correspondingEntries[i, j] = vecShape2[cur:(cur+B[i, j]-1)]
                    cur += B[i, j]
                end
            end
        end

        cur = 1
        for j in 1:size(B, 2)
            for i in 1:size(B, 1)
                if B[i, j] > 0
                    p[vecShape1[cur:(cur+B[i, j]-1)]] = correspondingEntries[i, j]
                    cur += B[i, j]
                end
            end
        end

        @assert length(p) == length(unique(p))

        combined = glue(sp1.F.F, sp2.F.F, p)
        # combined = glueFinite(N, sp1.F.F, sp2.F.F, p; labelFlags=false)

        combined === nothing && continue

        if combined isa Flag
            combined = QuantumFlag{T,Int}(combined => 1)
        end

        # @show sp1.T 
        # @show sp1.freePos
        # @show sp1.F.shape
        # @show sp2
        # fact = limit ? 1 : factorial(sp1.T.part[sp1.freePos]) * factorial(sp2.T.part[sp2.freePos])
        fact = 1

        for (comb, c) in combined.coeff
            if splitByOverlaps
                comb = (comb, sp1.F.F, sp2.F.F, B)
            end

            if !haskey(resUnsorted, comb)
                resUnsorted[comb] = c * combinedOverlapsReduced[B] // fact
            else
                resUnsorted[comb] += c * combinedOverlapsReduced[B] // fact
                if resUnsorted[comb] == 0
                    delete!(resUnsorted, comb)
                end
            end
        end
    end

    symmetrizedGraphs = Dict([])
    unSymmetrizedGraphsKeys = collect(keys(resUnsorted))
    symmetrizedGraphsKeys = nothing

    if !splitByOverlaps
        symmetrizedGraphsKeys = labelCanonically(unSymmetrizedGraphsKeys)
    else
        symmetrizedGraphsKeys = labelCanonically([g[1] for g in unSymmetrizedGraphsKeys])
    end

    for (i, k) in enumerate(symmetrizedGraphsKeys)
        if !splitByOverlaps
            if haskey(symmetrizedGraphs, k)
                symmetrizedGraphs[k] += resUnsorted[unSymmetrizedGraphsKeys[i]]
                if iszero(symmetrizedGraphs[k])
                    delete!(symmetrizedGraphs, k)
                end
            else
                symmetrizedGraphs[k] = resUnsorted[unSymmetrizedGraphsKeys[i]]
            end
        else
            if !haskey(symmetrizedGraphs, k)
                symmetrizedGraphs[k] = Dict()
            end
            if haskey(symmetrizedGraphs[k], unSymmetrizedGraphsKeys[i][2:end])
                symmetrizedGraphs[k][unSymmetrizedGraphsKeys[i][2:end]] += resUnsorted[unSymmetrizedGraphsKeys[i]]
                if iszero(symmetrizedGraphs[k][unSymmetrizedGraphsKeys[i][2:end]])
                    delete!(symmetrizedGraphs[k], unSymmetrizedGraphsKeys[i][2:end])
                end
            else
                symmetrizedGraphs[k][unSymmetrizedGraphsKeys[i][2:end]] = resUnsorted[unSymmetrizedGraphsKeys[i]]
            end
        end
    end

    if !limit
        for (k, p) in symmetrizedGraphs
            symmetrizedGraphs[k] = p * n^0
        end
    end

    return symmetrizedGraphs
end

function isAllowed(m::LasserreModel, F::T) where {T<:Flag}
    if m.parentModel !== nothing
        return isAllowed(m.parentModel, F)
    end
    return isAllowed(F)
end

function computeSDP!(m::LasserreModel{T,N,D}, reservedVerts::Int) where {T,N,D}#; maxVert = -1, useGroups = true, splitByOverlaps = false)
    #TODO: Parallelize better

    totalNum = Int64(sum(c * (c + 1) / 2 for c in length.(values(m.basis)); init = 0))

    t = 1

    splitByOverlaps = false

    doneCollecting = Threads.Event()

    collectData = Channel(Inf; spawn=true) do ch
        for (mu, i, j, blkSize, tmp) in ch
            for G in keys(tmp)
                if !haskey(m.sdpData, G)
                    m.sdpData[G] = Dict()
                end
                if !splitByOverlaps
                    if !haskey(m.sdpData[G], mu)
                        m.sdpData[G][mu] = spzeros(Rational{Int64}, blkSize, blkSize)
                    end
                    m.sdpData[G][mu][i, j] = tmp[G]
                else
                    for overlap in keys(tmp[G])
                        if !haskey(m.sdpData[G], overlap)
                            m.sdpData[G][overlap] = Dict()
                        end
                        if !haskey(m.sdpData[G][overlap], mu)
                            m.sdpData[G][overlap][mu] = spzeros(
                                Rational{Int64}, blkSize, blkSize
                            )
                        end
                        m.sdpData[G][overlap][mu][i, j] = tmp[G][overlap]
                    end
                end
            end
        end
        notify(doneCollecting)
    end

    limit = Base.Semaphore(max(1, floor(Threads.nthreads() / 2) - 1))
    println()
    for (cm, mu) in collect(enumerate(keys(m.basis)))
        blkSize = length(m.basis[mu])
        ijInd = [(i, j) for i in 1:blkSize for j in i:blkSize]

        muc = 1

        progressPrint = Channel{Nothing}(1000; spawn=true) do ch
            updateGap = 0.5
            lastUpdate = time()
            for _ in ch
                if time() - lastUpdate >= updateGap
                    print(
                        "\r$mu ($cm / $(length(keys(m.basis)))), $muc / $(length(ijInd)), total: $t / $totalNum        ",
                    )
                    lastUpdate = time()
                end
                t += 1
                muc += 1
            end
            print(
                "\r$mu ($cm / $(length(keys(m.basis)))), $(muc-1) / $(length(ijInd)), total: $(t-1) / $totalNum        \n",
            )
        end

        Threads.@threads for (i, j) in ijInd
            Base.acquire(limit) do
                put!(progressPrint, nothing)

                sp1 = m.basis[mu][i]
                sp2 = m.basis[mu][j]

                tmp = multiplyPolytabsAndSymmetrize(
                    m,
                    sp1,
                    sp2,
                    -1,#maxVert,
                    # N == :limit, # TODO: Limit
                    false,#splitByOverlaps,
                    false,#useGroups, #TODO: Optimize to be worth
                    # m.graphData[m.basis[mu][i][1]].rowAutomorphisms.fullGroup,
                    # m.graphData[m.basis[mu][j][1]].rowAutomorphisms.fullGroup,
                    reservedVerts
                )
                put!(collectData, (mu, i, j, blkSize, tmp))
            end
        end
        close(progressPrint)
    end
    close(collectData)
    # @info "Waiting for collection"

    @assert !isInducedFlag(T) "TODO: Reduction for induced flags for Lasserre hierarchy"

    return wait(doneCollecting)
    # @info "Notified"
end

function buildJuMPModel(
    m::LasserreModel{T,N,D}, replaceBlocks=Dict(), jumpModel=Model()
) where {T,N,D}
    b = modelBlockSizes(m)
    Y = Dict()

    constraints = Dict()

    for (mu, n) in b
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

    graphCoefficients = Dict()

    AT = typeof(sum(collect(values(Y))[1]))

    for G in keys(m.sdpData)
        # eG = AffExpr()
        # eG = GenericAffExpr{D, GenericVariableRef{D}}()
        eG = AT()
        for mu in keys(b)
            if haskey(m.sdpData[G], mu)
                for (i, j, c) in Iterators.zip(findnz(m.sdpData[G][mu])...)
                    i > j && continue
                    fact = (i == j ? D(1) : D(2))
                    add_to_expression!(eG, fact * D(c), Y[mu][i, j])
                    # add_to_expression!(eG, m.sdpData[G][mu][c],Y[mu][c])
                end
            end
        end
        graphCoefficients[G] = eG
    end

    # graphCoefficients = Dict(
    #     G => sum(
    #         dot(Y[mu], Symmetric(m.sdpData[G][mu])) for
    #         mu in keys(b) if haskey(m.sdpData[G], mu)
    #     ) for G in keys(m.sdpData)
    # )


    return (model=jumpModel, variables=graphCoefficients, blocks=Y, constraints=constraints)
end
