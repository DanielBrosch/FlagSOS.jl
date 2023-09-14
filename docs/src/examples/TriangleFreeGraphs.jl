#=
# Basic example: Mantel's theorem

The maximum edge density in triangle free graphs is well known to be ``\frac{1}{2}``, as was first proven by Mantel in 1907. Here we give an automatic proof.
=#

using FlagSOS

using Test #src

# ## Setting up the model
# We define the relevant graphs using their adjacency matrices.
edge = Graph(Bool[0 1; 1 0]);
triangle = Graph(Bool[0 1 1; 1 0 1; 1 1 0]);

# We start with an empty [`FlagModel`](@ref) of type [`Graph`](@ref), where we forbid the triangle graph (and all graphs containing it):
m = FlagModel{Graph}()
addForbiddenFlag(m, triangle)

# ## Choosing a relaxation
# Now we need to choose a hierarchy. One option is the Lasserre hierarchy, which we can attach to the model using [`addLasserreBlock!`](@ref).
addLasserreBlock!(m, 4);

# This results in a semidefinite programming problem with block sizes
@test modelSize(m).part == Int[5, 4, 4, 2, 2, 1, 1, 1] #src
modelSize(m)

# We want to maximize the `edge` density, which we can do by minimizing its negative
m.objective = -1 * edge

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

@test objective_value(jm.model) ≈ 0.5 #src
