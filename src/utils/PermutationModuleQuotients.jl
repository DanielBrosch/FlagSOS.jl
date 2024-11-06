using AbstractAlgebra: YoungTableau, Partition, @perm_str, matrix_repr
using AbstractAlgebra.Generic: collength, rowlength

function setTabEntry(Y, p, c)
    linPos = 0
    for i in 1:(p[1] - 1)
        linPos += Y.part[i]
    end
    linPos += p[2]
    return Y.fill[linPos] = c
end

# Calculating Kostka numbers
# number of semistandard tableaux of shape λ and content μ
# i.e. increasing rows, strictly increasing columns
# Also returns semistandard tableaux
function Kostka(λ, μ)
    if λ.n != μ.n
        return nothing
    end
    # Fill T up with num times c
    function fill(T, c, num)
        # Find potential rows with spaces
        potential = [0 for i in 0:collength(T, 1, 1)]
        lastNZ = [0 for i in 0:collength(T, 1, 1)]
        for i in 1:length(potential)
            # Find first zero in row i of T
            if T[i, 1] != 0
                lastNZ[i] = 1

                while rowlength(T, i, lastNZ[i]) > 0 && T[i, lastNZ[i]] != 0
                    lastNZ[i] += 1
                end
                if T[i, lastNZ[i]] == 0
                    lastNZ[i] -= 1
                end
                if rowlength(T, i, lastNZ[i]) == 0
                    continue
                end
            end

            potential[i] =
                min(rowlength(T, i, 1) + 1, (i > 1 ? lastNZ[i - 1] : 999999999999)) -
                lastNZ[i]
        end

        if num > sum(potential .* (potential .> 0))
            return []
        end

        numPotentialRows = sum(potential .> 0)
        res = []

        function fillRows(TC, r, remNum)
            for i in max(0, remNum - sum(potential[(r + 1):end])):min(potential[r], remNum)
                Tres = YoungTableau(TC.part, copy(TC.fill))
                for col in (lastNZ[r] + 1):(lastNZ[r] + i)
                    setTabEntry(Tres, (r, col), c)
                end
                if i == remNum
                    # display(Tres)
                    push!(res, Tres)
                else
                    fillRows(Tres, r + 1, remNum - i)
                end
            end
        end

        fillRows(T, 1, num)
        return res
    end

    TLast = [YoungTableau(λ, [0 for i in 1:(λ.n)])]
    for i in 1:length(μ.part)
        TCur = []
        for T in TLast
            TCur = union!(TCur, fill(T, i, μ[i]))
        end
        TLast = TCur
    end
    return (length(TLast), TLast)
end

# Find bigger shapes
function biggerShapes(λ)
    if length(λ) == 0
        return [λ]
    end

    firstRow = λ[1]
    res = [Partition([λ.n])]
    for i in 1:(λ.n - firstRow)
        for p in AllParts(i)
            if length(p) < length(λ) && p[1] <= λ.n - i
                tmp = vcat([λ.n - i], p)
                valid = true
                if i == λ.n - firstRow
                    for j in 1:length(tmp)
                        if tmp[j] > λ[j]
                            break
                        end
                        if tmp[j] < λ[j]
                            valid = false
                            break
                        end
                    end
                end
                if valid
                    push!(res, Partition(tmp))
                end
            end
        end
    end
    return sort!(res)
end

function shiftElement(p, by=1)
    return vcat(collect(1:by), p .+ by)
end

function insertElement(p, at=1)
    # return vcat(collect(1:by), p .+ by)
    return vcat(p[1:at-1], [at], p[at:end] .+ 1)
end

function shiftGroup(F)
    return [Perm(vcat([1], p.d .+ 1)) for p in F]
end

function generateGroup(generator, size, hasRepMat=false)
    if size == 1
        return generator
    end
    nextIndex = length(generator)
    if !hasRepMat
        generator = [g.d for g in generator]
        res = copy(generator)
        lastIndex = 0

        while nextIndex < size
            union!(res, f[g] for f in res[(lastIndex + 1):length(res)], g in generator)
            lastIndex = nextIndex
            nextIndex = length(res)
        end
        return AbstractAlgebra.perm.(res)
    else
        representation = Dict([g[1] => g[2] for g in generator])
        res = [g[1] for g in generator]
        lastIndex = 0
        while nextIndex < size
            for f in res[(lastIndex + 1):length(res)]
                for g in generator
                    # p = g[1] * f
                    p = [f[g[1][i]] for i in 1:length(g[1])]
                    if !in(p, res)
                        push!(res, p)
                        merge!(
                            representation,
                            Dict([p => representation[f] * representation[g[1]]]),
                        )
                    end
                end
            end
            lastIndex = nextIndex
            nextIndex = length(res)
        end
        return (res, representation)
    end
end

function semiTabPermMat(K, p)
    tmpRes = Dict()

    function applyPermToSemiTabV3(semiTab, p)
        t0 = YoungTableau(semiTab.part, [p[i] for i in semiTab.fill])
        # @show t0

        function isSemiUpToi(t, i)
            last = zeros(Int64, size(t, 2))

            for j in 1:i
                current = vec(sum(t .== j; dims=1))
                newLast = last + current
                if maximum(current) > 1 || !issorted(newLast; rev=true)
                    return false
                end
                last = newLast
            end
            return true
        end

        function decomp(t, ignoreT)
            return get!(tmpRes, (t, ignoreT)) do
                iFixed = [t]

                for i in 1:maximum(t.fill)
                    tmp = []
                    for ti in iFixed
                        tiTmp = []
                        for j in 1:size(ti, 1)
                            @inbounds @views posPositions = findall(ti[j, :] .>= i)
                            @inbounds @views numPos = count(ti[j, :] .== i)
                            rowOptions = []
                            for c in combinations(posPositions, numPos)
                                @inbounds @views tmpRow = copy(ti[j, :])
                                @inbounds tmpRow[c] .= i
                                @inbounds @views tmpRow[setdiff(posPositions, c)] = filter(
                                    x -> x != i, ti[j, posPositions]
                                )
                                push!(rowOptions, reshape(tmpRow, 1, :))
                            end

                            if j == 1
                                tiTmp = rowOptions
                            else
                                tiTmp = [vcat(a, b) for a in tiTmp for b in rowOptions]
                            end
                        end
                        tmp = vcat(tmp, filter(x -> isSemiUpToi(x, i), tiTmp))
                    end
                    iFixed = tmp
                end

                # sort columns and calculate signs
                res = Dict()
                for ti in iFixed
                    s = 1
                    for j in 1:size(ti, 2)
                        col = ti[1:(collength(t, 1, j) + 1), j]
                        if length(col) > 1
                            s *= (-1)^sum(c2 < c1 for (c1, c2) in combinations(col, 2))
                        end
                        sCol = sort(col)
                        for i in 1:length(sCol)
                            ti[i, j] = sCol[i]
                        end
                    end

                    yti = YoungTableau(t.part, filter(x -> x != 0, vec(ti')))

                    if !ignoreT || yti != t
                        res[yti] = get(res, yti, 0) + s
                    end
                end

                fullres = deepcopy(res)

                for (ti, c) in res
                    tmp = decomp(ti, true)
                    for (tj, c2) in tmp
                        fullres[tj] = get(fullres, tj, 0) - c * c2
                    end
                end

                fullres
            end
        end
        return collect(decomp(t0, false))
    end

    mat = zeros(Int64, length(K[2]), length(K[2]))
    #Threads.@threads 
    for (i, t) in collect(enumerate(K[2]))
        # print("$i / $(K[1])\r")
        res = applyPermToSemiTabV3(t, p)
        if res !== nothing
            for r in res
                c = findfirst(x -> x == r[1], K[2])
                mat[c, i] += r[2]
            end
        end
    end
    return mat
end

function decomposeModule(lambda, rowAut)
    blkSizes = []
    blks = []
    bs = biggerShapes(lambda)

    ## Full sym:
    sdpBasisFull = Dict()

    for (i, mu) in enumerate(bs)
        K = Kostka(mu, lambda)

        reynolds = zeros(Int64, K[1], K[1])
        if rowAut.size > 1
            generator = []
            for p in rowAut.gen
                push!(generator, (p, semiTabPermMat(K, p)))
            end
            fullGroup = generateGroup(generator, rowAut.size, true)
            for p in fullGroup[1]
                reynolds += fullGroup[2][p]
            end
        else
            for i in 1:K[1]
                reynolds[i, i] = 1
            end
        end
        r = rank(reynolds)
        push!(blkSizes, r)
        push!(blks, reynolds)
    end

    for (i, mu) in enumerate(bs)
        K = Kostka(mu, lambda)

        R = blks[i]

        inds = findColSpanningSetV3(R)
        if length(inds) > 0
            sdpBasisFull[mu] = []

            for i in inds
                push!(sdpBasisFull[mu], K[2][i])
            end
        end
    end

    return sdpBasisFull
end

# Algorithm of Dion Gijswijt, generalized as described in Daniel Brosch's thesis
function symPolytabloidProduct(
    t1::AbstractAlgebra.Generic.YoungTableau{Int64},
    t2::AbstractAlgebra.Generic.YoungTableau{Int64},
    lambda::Vector{T}=Int8.(
        t1.part.part[1] > t2.part.part[1] ? t1.part.part : t2.part.part
    ),
    limit=false,
) where {T}
    m = max(maximum(t1), maximum(t2))
    lambda = vcat(lambda, [zero(lambda[1]) for i in (length(lambda) + 1):(m + 1)])

    # @show lambda
    # @assert issorted(lambda, rev = true)
    @assert issorted(lambda, lt = (x,y)->x>y)

    function move(A::Matrix{T}, i::Int, j::Int, k::Int, l::Int)
        res = copy(A)
        res[i, j] -= 1
        res[k, l] += 1
        return res
    end

    function pMat(p::Perm{Int64})
        t = zeros(T, m, m)
        for (i, d) in enumerate(p.d)
            t[i, d] = 1
        end
        return t
    end

    function oDet(n::Int)
        return Dict{Matrix{T},T}(pMat(P) => sign(P) for P in SymmetricGroup(n))
    end

    function mink(As::Dict{Matrix{T},T}, Bs::Dict{Matrix{T},T})
        t = Dict{Matrix{T},T}()
        for (A, ca) in As
            for (B, cb) in Bs
                C = A + B
                t[C] = get!(t, C, 0) + ca * cb
            end
        end
        return t
    end

    res = Dict{Matrix{T},T}(zeros(T, m, m) => 1)
    for k in 1:m
        t = lambda[k] - lambda[k + 1]
        if !iszero(t)
            if k == 1
                M = zeros(T, m, m)
                M[1, 1] = t
                res = Dict{Matrix{T},T}(M => 1)
            else
                oD = oDet(k)
                map!(x -> x * factorial(k), values(oD))
                for i in 1:convert(Int, t)
                    res = mink(res, oD)
                end
            end
        end
    end

    function r(s, j)
        return (
            (j <= length(t1.part) && (!limit || j > 1)) ? (count(x -> x == s, t1[j, :])) : 0
        )
    end
    function u(s, j)
        return (
            (j <= length(t2.part) && (!limit || j > 1)) ? (count(x -> x == s, t2[j, :])) : 0
        )
    end

    # factor out the size of the column stabilizer
    fact = prod([factorial(t) for t in conj(t1.part).part])
    # fact = prod([factorial(t) for t in conj(t1.part).part])*prod([factorial(t) for t in conj(t2.part).part])
    # @show fact
    for j in (m - 1):-1:1
        # First loop depends on order, second does not matter
        for s in (j + 1):m
            usj = u(s, j)
            
            fact *= factorial(usj)
            # @show fact
            
            for k in 1:usj
                res2 = Dict{Matrix{T},T}()
                for (B, c) in res
                    for nz in findall(!iszero, B[:, j])
                        B2 = move(B, nz, j, nz, s)
                        res2[B2] = get!(res2, B2, 0) + c * B[nz, j]
                    end
                end
                res = res2
            end
        end
    end
    
    for j in (m - 1):-1:1
        # First loop depends on order, second does not matter
        for s in (j + 1):m
            rsj = r(s, j)

            fact *= factorial(rsj)
            
            for k in 1:rsj
                res2 = Dict{Matrix{T},T}()
                for (B, c) in res
                    for nz in findall(!iszero, B[j, :])
                        B2 = move(B, j, nz, s, nz)
                        res2[B2] = get!(res2, B2, 0) + c * B[j, nz]
                    end
                end
                res = res2
            end
        end
    end

    if limit
        limitDifMat = zeros(Int, m, m)
        for i in 2:m
            limitDifMat[i, 1] = count(x -> x == i, t1[1, :])
            limitDifMat[1, i] = count(x -> x == i, t2[1, :])
        end

        res = Dict{Matrix{T},T}(m + limitDifMat => c for (m, c) in res)
    end

    filter!(x -> !iszero(x.second), res)

    return res, fact
end
