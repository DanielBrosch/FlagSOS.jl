#=
# Constrained example: Caccetta Haeggkvist conjecture
The maximum minimum outdegree of a directed graph (without digons) without directed triangles is conjectured to be ``\frac{1}{3}``:
```math
\begin{aligned}
\frac{1}{3}=\max_{G \text{ directed graph}} &r\\
\text{s.t.}\enspace & G \text{ has no directed triangles},\\
& \text{the relative outdegree of every vertex is at least }r.
\end{aligned}
```
Here we compute an upper bound using a basic application of flag algebras. A more advanced application of the method lead to current best bound.  
=#

using FlagSOS

using Test #src

# ## Setting up the model
# We work with directed graphs without digons.
const Digraph = DirectedGraph{false}
# We define the relevant graphs using their adjacency matrices.
directedEdge = Digraph(Bool[0 1; 0 0]) # o -> o
directedTriangle = Digraph(Bool[0 1 0; 0 0 1; 1 0 0]) # x -> o -> o -> x

# We start with an empty [`FlagModel`](@ref) of type [`DirectedGraph`](@ref), where we forbid the directed triangle:
m = FlagModel{Digraph}()
addForbiddenFlag!(m, directedTriangle)

# ## Choosing a relaxation
# Now we need to choose a hierarchy. One option is the Lasserre hierarchy, which we can attach to the model using [`addLasserreBlock!`](@ref).
addLasserreBlock!(m, 4);

# This results in a semidefinite programming problem with block sizes
modelSize(m)

# We obtain an equivalent formulation of the conjecture the following way: We remove additional outgoing edges, until every vertex has relative outdegree exactly r. Then r is exactly the edge density of the digraph, i.e. we want to maximize the density of `directedEdge`. This we can do by minimizing its negative
m.objective = -1 * directedEdge

# We add the constraint that every vertex has relative outdegree identical to the (directed) edge density of the graph.  
const lDigraph = PartiallyLabeledFlag{Digraph}
e1 = lDigraph(Bool[0 1; 0 0]; n=1) # 1 -> o
eL = lDigraph(Bool[0 1; 0 0]; n=0) # o -> o

qm2 = FlagSOS.addEquality!(m, e1 - eL, 4);

# Finally, we compute the coefficients of the SDP.
computeSDP!(m)

# ## Solving the SDP 
# We solve the relaxation using [Hypatia](https://github.com/chriscoey/Hypatia.jl).
using Hypatia, JuMP
jm = buildJuMPModel(m)
set_optimizer(jm.model, Hypatia.Optimizer)
optimize!(jm.model)
termination_status(jm.model)
#-
objective_value(jm.model)

@test objective_value(jm.model) ≈ 0.3869 atol = 5 #src
