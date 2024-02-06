using FlagSOS
using Test
using Aqua
using Documenter

"""
    _include_sandbox(filename)
Include the `filename` in a temporary module that acts as a sandbox. (Ensuring
no constants or functions leak into other files.)
"""
function _include_sandbox(filename)
    mod = @eval module $(gensym()) end
    return Base.include(mod, filename)
end

function _file_list(full_dir, relative_dir, extension)
    return map(
        file -> joinpath(relative_dir, file),
        filter(file -> endswith(file, extension), sort(readdir(full_dir))),
    )
end

function _test_directory(dir)
    rm.(_file_list(dir, dir, ".md"))
    for filename in _file_list(dir, dir, ".jl")
        # `include` the file to test it before `#src` lines are removed. It is
        # in a testset to isolate local variables between files.
        Test.@testset "$(filename)" begin
            _include_sandbox(filename)
        end
    end
    return nothing
end

@testset "FlagSOS.jl" begin
    @testset "Code quality (Aqua.jl)" begin
        Aqua.test_all(FlagSOS; ambiguities=(imported = false), deps_compat=(check_extras=false))#ignore=[Test, Aqua]))
    end

    @testset "Doctests" begin
        doctest(FlagSOS)
    end

    @testset "Examples" begin
        _test_directory.(joinpath(@__DIR__, "..", "docs", "src", "examples"))
    end

    @testset "Harmonic Flags" begin 
        _include_sandbox("src/HarmonicFlags.jl")
    end
end
