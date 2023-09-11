using FlagSOS
using Test
using Aqua

@testset "FlagSOS.jl" begin
    @testset "Code quality (Aqua.jl)" begin
        Aqua.test_all(FlagSOS)
    end
    # Write your tests here.
end
