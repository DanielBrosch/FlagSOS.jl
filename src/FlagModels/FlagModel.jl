export FlagModel,
    addLasserreBlock!,
    addForbiddenFlag!,
    addInequality!,
    addInequality_Lasserre!,
    addEquality!,
    buildStandardModel,
    addRazborovBlock!,
    addBinomialBlock!,
    buildClusteredLowRankModel

using ClusteredLowRankSolver

"""
    FlagModel{T <: Flag, N, D} <: AbstractFlagModel{T, N, D}

A Flag-model with internal Flag type 'T'.

# Parameters
- `T`: Target Flag type
- `N`: Limit parameter, see `AbstractFlagModel`
- `D`: Data type of coefficients of the final optimization problem

"""
mutable struct FlagModel{T<:Flag,N,D} <: AbstractFlagModel{T,N,D}
    subModels::Vector{AbstractFlagModel{T,N,D}}
    forbiddenFlags::Set{T}
    objective::Union{QuantumFlag{T,D},Nothing}
    function FlagModel{T}() where {T<:Flag}
        return new{T,:limit,Int}(AbstractFlagModel{T,:limit,Int}[], Set{T}(), nothing)
    end
    function FlagModel{T,D}() where {T<:Flag,D}
        return new{T,:limit,D}(AbstractFlagModel{T,:limit,D}[], Set{T}(), nothing)
    end
    function FlagModel{T,N,D}() where {T<:Flag,D,N}
        return new{T,N,D}(AbstractFlagModel{T,N,D}[], Set{T}(), nothing)
    end
end

function Base.show(io::IO, m::FlagModel{T,N,D}) where {T,N,D}
    println(io, "Flag algebra model of type $T")
    if m.objective !== nothing
        println(io, "Objective: $(m.objective)")
    end
    return Base.show.(io, m.subModels)
end

function addForbiddenFlag!(m::FlagModel{T,N,D}, F::T) where {T<:Flag,N,D}
    #TODO: If non-induced, forbid all graphs that can be obtained by adding edges, as well.
    Fl = labelCanonically(F)
    return push!(m.forbiddenFlags, Fl)
    # for ms in m.subModels
    #     addForbiddenFlag!(ms, Fl)
    # end
end

function computeSDP!(m::FlagModel, reservedVerts::Int)
    return computeSDP!.(m.subModels, reservedVerts)
end

function isAllowed(m::FlagModel{T,N,D}, F::T) where {T<:Flag,N,D}
    return isAllowed(F) && !any(f -> isSubFlag(f, F), m.forbiddenFlags)
end

function isAllowed(m::FlagModel{T,N,D}, F::EdgeMarkedFlag{T}) where {T<:Flag,N,D}
    return isAllowed(F) && !any(f -> isSubFlag(f, F), m.forbiddenFlags)
end

function isAllowed(m::FlagModel{T,N,D}, F::PartiallyLabeledFlag{T}) where {T<:Flag,N,D}
    F2 = labelCanonically(F.F)
    return isAllowed(m, F2)
end

"""
   addLasserreBlock!(m::FlagModel{T,N,D}) where {T<:Flag,N,D}

Adds an empty Lasserre block of internal flag type 'T' to 'm' and returns it. One should then use 'addFlag' to add generators to the block. 
"""
function addLasserreBlock!(m::FlagModel{T,N,D}) where {T<:Flag,N,D}
    lM = LasserreModel{T,N,D}(m)
    push!(m.subModels, lM)
    return lM
end

"""
   addLasserreBlock!(m::FlagModel{T,N,D}, maxEdges::Int; maxVertices = maxEdges * maxPredicateArguments(T)) where {T<:Flag,N,D}

Adds a symmetry reduced Lasserre block of internal flag type 'T' to 'm' and returns it. All flags with up to 'floor(maxEdges/2)' edges (resp. true predicates) with optionally at most 'floor(maxVertices/2)' vertices are added as generators of the block. The resulting hierarchy contains flags with at most 'maxEdges' edges and 'maxVertices' vertices.
"""
function addLasserreBlock!(
    m::FlagModel{T,N,D}, maxEdges; maxVertices=maxEdges * maxPredicateArguments(T)
) where {T<:Flag,N,D}
    lM = LasserreModel{T,N,D}(m)
    push!(m.subModels, lM)

    Fs = generateAll(T, Int(floor(maxVertices / 2)), Int.(floor.(maxEdges / 2)))
    display(Fs)
    for F in Fs
        if isAllowed(m, F)
            addFlag!(lM, F)
        end
    end

    return lM
end

function addRazborovBlock!(
    m::FlagModel{T,N,D}, lvl; maxLabels=lvl, maxBlockSize=Inf
) where {T<:Flag,N,D}
    rM = RazborovModel{T,N,D}(m)
    push!(m.subModels, rM)
    computeRazborovBasis!(rM, lvl; maxLabels=maxLabels, maxBlockSize=maxBlockSize)

    return rM
end

function addBinomialBlock!(m::FlagModel{T,N,D}, maxVerts, maxEdges) where {T<:Flag,N,D}
    rM = BinomialSquares{T,N,D}(maxVerts, maxEdges)
    push!(m.subModels, rM)
    return rM
end

function addInequality!(
    m::FlagModel{T,N,D}, g::QuantumFlag{U,D}, baseModel::B
) where {T<:Flag,U<:Flag,N,D,B<:AbstractFlagModel{U,N,D}}
    gl = labelCanonically(g)
    qM = QuadraticModule{T}(baseModel, gl)
    push!(m.subModels, qM)
    return qM
end

function addInequality_Lasserre!(
    m::FlagModel{T,N,D},
    g::QuantumFlag{T,D},
    maxEdges;
    maxVertices=size(g) +
                floor((maxEdges - countEdges(g)[1]) / 2) * maxPredicateArguments(T),
) where {T<:Flag,N,D}
    gl = labelCanonically(g)

    genMaxEdges = Int(floor((maxEdges - countEdges(gl)[1]) / 2))
    genMaxVertices = Int(floor((maxVertices - size(gl)) / 2))

    lM = LasserreModel{T,N,D}()
    Fs = generateAll(T, genMaxVertices, genMaxEdges)

    for F in Fs
        if isAllowed(m, F)
            addFlag!(lM, F)
        end
    end

    qM = QuadraticModule{T}(lM, gl)
    push!(m.subModels, qM)
    return qM
end

function addInequality_Lasserre!(
    m::FlagModel{T,N,D},
    g::QuantumFlag{PartiallyLabeledFlag{T},D},
    maxEdges;
    maxVertices=size(g) +
                floor((maxEdges - countEdges(g)[2]) / 2) * maxPredicateArguments(T),
) where {T<:Flag,N,D}
    gl = labelCanonically(g)

    genMaxEdges = Int(floor((maxEdges - countEdges(gl)[2]) / 2))
    genMaxVertices = Int(floor((maxVertices - size(gl)) / 2))

    lM = LasserreModel{PartiallyLabeledFlag{T},N,D}()

    @show genMaxEdges
    @show genMaxVertices

    Fs = generateAll(
        PartiallyLabeledFlag{T},
        numLabels(gl) + genMaxVertices,
        [numLabels(gl), genMaxEdges],
    )

    filter!(x -> x.n == numLabels(gl), Fs)

    for F in Fs
        if isAllowed(m, F)
            addFlag!(lM, F)
        end
    end

    qM = QuadraticModule{T,PartiallyLabeledFlag{T}}(lM, gl, 0)#numLabels(gl))
    push!(m.subModels, qM)
    return qM
end

function addEquality!(
    m::FlagModel{T,N,D},
    g::QuantumFlag{PartiallyLabeledFlag{T},D},
    maxEdges;
    maxVertices=size(g) +
                (maxEdges - countEdges(g)[2]) * maxPredicateArguments(T),
) where {T<:Flag,N,D}
    gl = labelCanonically(g)

    genMaxEdges = Int(floor((maxEdges - countEdges(gl)[2])))
    genMaxVertices = Int(floor((maxVertices - size(gl))))

    qM = EqualityModule{T,PartiallyLabeledFlag{T},N,D}(gl, 0)#numLabels(gl))

    Fs = generateAll(
        PartiallyLabeledFlag{T},
        genMaxVertices + numLabels(gl),
        [numLabels(gl), genMaxEdges],
    )

    filter!(x -> x.n == numLabels(gl), Fs)

    for F in Fs
        if isAllowed(m, F)
            push!(qM.basis, F)
        end
    end

    push!(m.subModels, qM)

    return qM
end

function addEquality!(
    m::FlagModel{T,N,D},
    g::QuantumFlag{T,D},
    maxEdges;
    maxVertices=size(g) +
                (maxEdges - countEdges(g)[1]) * maxPredicateArguments(T),
) where {T<:Flag,N,D}
    gl = labelCanonically(g)

    genMaxEdges = Int(floor((maxEdges - countEdges(gl)[1])))
    genMaxVertices = Int(floor((maxVertices - size(gl))))

    qM = EqualityModule{T,T,N,D}(gl)

    Fs = generateAll(T, genMaxVertices, genMaxEdges)

    for F in Fs
        if isAllowed(m, F)
            push!(qM.basis, F)
        end
    end

    push!(m.subModels, qM)

    return qM
end

function buildJuMPModel(
    m::FlagModel{T,N,D}, replaceBlocks=Dict(), jumpModel=Model(), addBoundVars=false
) where {T<:Flag,N,D}
    variables = Dict()
    blocks = []
    constraints = []
    i = 1
    for sM in m.subModels
        jm, v, b, c = buildJuMPModel(
            sM, haskey(replaceBlocks, i) ? replaceBlocks[i] : Dict(), jumpModel
        )
        mergewith!(+, variables, v)
        push!(blocks, b)
        constraints = push!(constraints, c)
        i += 1
    end

    if addBoundVars
        @warn "Adding bound variables"
        for F in keys(variables)
            fl = @variable(jumpModel, base_name = "lower$F", lower_bound = 0)
            fu = @variable(jumpModel, base_name = "upper$F", lower_bound = 0)
            variables[F] += fl - fu
            variables[one(F)] += fu
        end
    end

    if m.objective !== nothing
        push!(constraints, Dict())
        objL = labelCanonically(m.objective)
        for (G, c) in objL.coeff
            if !iszero(c) && !haskey(variables, G)
                error(
                    "Not all Flags in the objective appear in the model! Add more generators.",
                )
                return nothing
            end
        end
        for (G, c) in variables
            if isAllowed(m, G) && (G != T())# || T() in keys(objL.coeff))
                @assert G == labelCanonically(G)
                ## TODO: For some bases, such as induced and non-induced, <= is enough here.
                # push!(constraints, c == (haskey(objL.coeff, G) ? objL.coeff[G] : 0))  
                # push!(constraints, c <= (haskey(objL.coeff, G) ? objL.coeff[G] : 0))
                constraints[end][G] = @constraint(jumpModel, c == get(objL.coeff, G, 0))
                # constraints[end][G] = @constraint(jumpModel, c <= get(objL.coeff, G, 0))
            end
        end
    end

    if m.objective !== nothing
        if !(one(T) in keys(m.objective.coeff))
            @objective(jumpModel, Min, variables[one(T)])
        else
            # @objective(jumpModel, Min, 0)
            @objective(jumpModel, Min, variables[one(T)] - m.objective.coeff[one(T)])
        end
    end
    return (model=jumpModel, variables=variables, blocks=blocks, constraints=constraints)
end

function roundResults(m::FlagModel, jumpModel, variables, blocks, constraints; prec=1e-5)
    ex = []

    for i in 1:length(m.subModels)
        exi = roundResults(
            m.subModels[i], jumpModel, variables, blocks[i], constraints[i]; prec=prec
        )
        push!(ex, exi)
    end

    return ex
end

function modelSize(m::FlagModel)
    return Partition(vcat([modelSize(sM).part for sM in m.subModels]...))
end

function modelBlockSizes(m::FlagModel)
    res = Dict()

    for (i, sm) in enumerate(m.subModels)
        for (mu, n) in modelBlockSizes(sm)
            res[(i, mu)] = n
        end
    end
    return res
end


function buildStandardModel(m::FlagModel{T,N,D}) where {T<:Flag,N,D}
    #TODO: Quotient when using InducedFlags
    obj = labelCanonically(m.objective)
    vars = union([collect(keys(sM.sdpData)) for sM in m.subModels]...)
    filter!(F -> isAllowed(m, F), vars)
    blocks = Dict()
    blockSizes = Dict()
    for (i, sM) in enumerate(m.subModels)
        b = modelBlockSizes(sM)
        for mu in keys(b)
            blockSizes[(i, mu)] = b[mu] # negative = free variable
            if b[mu] >= 0
                blocks[(i, mu)] = Dict(
                    G => Symmetric(Matrix(sM.sdpData[G][mu])) for
                    G in vars if haskey(sM.sdpData, G) && haskey(sM.sdpData[G], mu)
                )
            else
                @assert b[mu] == -1 "TODO: Need to implement bigger free blocks"
                blocks[(i, mu)] = Dict(
                    G => Symmetric(Matrix([sM.sdpData[G][mu];;])) for
                    G in vars if haskey(sM.sdpData, G) && haskey(sM.sdpData[G], mu)
                )
            end
        end
    end

    return (obj=obj, vars=vars, blocks=blocks, blockSizes=blockSizes)
end

function buildClusteredLowRankModel(m::FlagModel{T,N,D}) where {T,N,D}

    obj, vars, blocks, blockSizes = buildStandardModel(m)
    o = T()


    varDicts = Dict(
        G => Dict{Any, Any}(
            mu => Matrix(B[G])
            for (mu, B) in blocks if haskey(B, G) && blockSizes[mu] > 0
        )
        for G in vars
    )

    # bound variables
    # for G in vars
    #     if G != o
    #         varDicts[G][(:lower, G)] = [1;;]
    #         varDicts[G][(:upper, G)] = [-1;;]
    #         varDicts[o][(:upper, G)] = [1;;]
    #     end
    # end

    freeVarDicts = Dict(
        G => Dict(
            mu => B[G][1, 1]
            for (mu, B) in blocks if haskey(B, G) && blockSizes[mu] < 0
        )
        for G in vars
    )



    clObj = Objective(get(obj.coeff, o, 0), get(varDicts, o, Dict()), freeVarDicts[o])
    clCons = Constraint[]

    for G in vars
        G == o && continue
        # @show G
        # display(varDicts[G])
        # display(freeVarDicts[G])
        c = Constraint(get(obj.coeff, G, 0), varDicts[G], freeVarDicts[G])
        # @show c
        push!(clCons, c)
    end

    return Problem(Minimize(clObj), clCons)
end

function facialReduction(m::AbstractFlagModel)
    return error("TODO")
end

function verifySOS(m::FlagModel{T,N,D}, sol::Vector; io::IO=stdout) where {T,N,D}
    @assert length(sol) == length(m.subModels)

    Base.show(io, m)
    println()

    tmp = labelCanonically(
        sum(verifySOS(m.subModels[i], sol[i]; io=io) for i in 1:length(m.subModels))
    )

    println(io, "SOS result:")
    println(io, "$(tmp) >= 0")

    err = Rational{BigInt}(0)
    constTerm = Rational{BigInt}(0)
    for (F, c) in tmp.coeff
        if F == one(T)
            constTerm += c
        else
            d = get(m.objective.coeff, F, Rational{BigInt}(0)) - c
            # if d > 0 
            #     err += d
            # end
            if d > 0
                err += abs(d)
            end
        end
    end

    println(io, "\nSummary:")
    Base.show(io, m)

    println(io, "Constant:")
    println(io, "$(constTerm)")

    println(io, "Error:")
    println(io, "$(err)")

    if haskey(m.objective.coeff, T())
        constTerm -= m.objective.coeff[T()]
    end
    res = constTerm + err + m.objective
    println(io, "Final rigorous bound:")
    println(io, "$(res) >= 0")

    println(io, "Floating point bound (rounded appropriately):")
    first = true
    for (g, cR) in res.coeff
        c = Float64(cR, RoundUp)
        if c < 0 || (first && c > 0)
            print(io, " $c*$g")
            first = false
        else
            print(io, " + $c*$g ")
        end
    end
    println(io, " >= 0")

    return res
end
