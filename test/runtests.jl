using FlagSOS
using Test
using Aqua
using Documenter

@testset "FlagSOS.jl" begin
    @testset "Code quality (Aqua.jl)" begin
        Aqua.test_all(FlagSOS; ambiguities = (imported = false))
    end

    @testset "Doctests" begin
        doctest(FlagSOS)
    end
    # Write your tests here.
end
