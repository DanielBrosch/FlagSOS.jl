#=
# Finite + high precision example: Error correcting codes

A constant weight [error correcting code](https://en.wikipedia.org/wiki/Error_correction_code) of length `N`, distance `D` and weight `W` is a set of binary words of length `N`, each of which has exactly `W` ones, where every pair of words differs in at least `D` coordinates. Here we bound the maximum cardinality of such a code, and solve the SDP to a high precision.
=#

using FlagSOS
using Test #src

# ## Setting up the model

N = 11 # length
W = 3  # weight 
D = 4; # distance

# The type ConstantWeightCode{W,D} models all codes with constant weight `W` and minimum distance `D`, independent of its length `N`.

const WDCode = ConstantWeightCode{W,D}

# We start by creating an empty [`FlagModel`](@ref) for `WDCode`s of length `N`. Since `N` is finite, we need `Rational{Int}` coefficients.
m = FlagModel{WDCode,N,Rational{Int}}();

# We want to maximize the cardinality of the code, i.e. the density of the subcode containing just one word of weight `W`. 
e = WDCode(ones(Bool, 1, W))
m.objective = -1 * e

# ## Initializing the Razborov hierarchy
# We chose to work with the Razborov hierarchy at level `6`, which is based on densities of subcodes fully contained in `lvl` vertices of the code. This is the same hierarchy [Flagmatic](http://lidicky.name/flagmatic/) uses. 
lvl = 6
rM = addRazborovBlock!(m, lvl)
modelBlockSizes(rM)

@test modelSize(rM).part == [10, 4, 4, 2, 1, 1, 1, 1, 1, 1] #src

# We still need to compute the coefficients of the actual optimization problem
computeSDP!(m)

# ## Solving the SDP
# Now we can solve it to a high precision
using Hypatia, JuMP, GenericLinearAlgebra
setprecision(256)
M = buildJuMPModel(m, Dict(), GenericModel{BigFloat}());
set_optimizer(M.model, Hypatia.Optimizer{BigFloat})
optimize!(M.model)

#-
termination_status(M.model)
# We need to turn the density of the code to its cardinality
objective_value(M.model) * binomial(N, W)
@test objective_value(M.model) * binomial(N, W) ≈ 18.33333333333 #src
