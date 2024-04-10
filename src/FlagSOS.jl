
# TODO: check out @inbounds
"""
    module FlagSOS

Module for customizable Flag-Sum of Squares problems:
Change the type of Flag-Algebra, e.g. graphs, hypergraphs, permutations, order types.
Generate fully symmetry reduced finite n, infinite n, flexible Flag SOS hierarchies.
"""
module FlagSOS

using AbstractAlgebra
using Combinatorics
using LinearAlgebra
using JuMP

include("utils/RoundToRationalPSD.jl")
include("utils/Nauty.jl")
include("FlagAlgebras/AbstractFlagAlgebra.jl")
include("FlagModels/AbstractFlagModel.jl")

end #module
