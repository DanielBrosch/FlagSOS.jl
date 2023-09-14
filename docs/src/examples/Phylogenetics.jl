#=
# TODO: Clean up tree example
=#

using FlagSOS

using Test #src

# ## Setting up the model
# We define the relevant graphs using their adjacency matrices.
# edge = Graph(Bool[0 1; 1 0]);
# triangle = Graph(Bool[0 1 1; 1 0 1; 1 1 0]);

# We start with an empty [`FlagModel`](@ref) of type [`Graph`](@ref), where we forbid the triangle graph (and all graphs containing it):
m = FlagModel{BinaryTreeFlag}()
T = BinaryTreeFlag(BinaryTree(BinaryTree(), BinaryTree(BinaryTree(BinaryTree(),BinaryTree()),BinaryTree(BinaryTree(),BinaryTree()))))

# ## Choosing a relaxation
# Now we need to choose a hierarchy. One option is the Lasserre hierarchy, which we can attach to the model using [`addLasserreBlock!`](@ref).
# addRazborovBlock!(m, 4);

# # This results in a semidefinite programming problem with block sizes
# modelSize(m)

# # We want to maximize the `edge` density, which we can do by minimizing its negative
# m.objective = -1 * T

# # Finally, we compute the coefficients of the SDP.
# computeSDP!(m)

# # ## Solving the SDP 
# # We solve the relaxation using [Hypatia](https://github.com/chriscoey/Hypatia.jl).
# using Hypatia, JuMP
# jm = buildJuMPModel(m)
# set_optimizer(jm.model, Hypatia.Optimizer)
# optimize!(jm.model)
# termination_status(jm.model)
# #-
# objective_value(jm.model)

# @test objective_value(jm.model) ≈ 0.5 #src
