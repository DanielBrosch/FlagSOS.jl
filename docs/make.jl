using FlagSOS
using Documenter
using Literate
using Test

DocMeta.setdocmeta!(FlagSOS, :DocTestSetup, :(using FlagSOS); recursive=true)

## Use Literate.jl to generate examples (functions modified from https://github.com/jump-dev/JuMP.jl/blob/master/docs/make.jl)

function _file_list(full_dir, relative_dir, extension)
    return map(
        file -> joinpath(relative_dir, file),
        filter(file -> endswith(file, extension), sort(readdir(full_dir))),
    )
end

"""
    _include_sandbox(filename)
Include the `filename` in a temporary module that acts as a sandbox. (Ensuring
no constants or functions leak into other files.)
"""
function _include_sandbox(filename)
    mod = @eval module $(gensym()) end
    return Base.include(mod, filename)
end

function _literate_directory(dir)
    rm.(_file_list(dir, dir, ".md"))
    for filename in _file_list(dir, dir, ".jl")
        # `include` the file to test it before `#src` lines are removed. It is
        # in a testset to isolate local variables between files.
        Test.@testset "$(filename)" begin
            _include_sandbox(filename)
        end
        Literate.markdown(
            filename,
            dir;
            documenter = true,
            credit = true,
        )
    end
    return nothing
end

_literate_directory.(joinpath(@__DIR__, "src", "examples"))

makedocs(;
    modules=[FlagSOS],
    authors="Daniel Brosch <73886037+DanielBrosch@users.noreply.github.com> and contributors",
    repo="https://github.com/DanielBrosch/FlagSOS.jl/blob/{commit}{path}#{line}",
    sitename="FlagSOS.jl",
    format=Documenter.HTML(;
        prettyurls=get(ENV, "CI", "false") == "true",
        canonical="https://DanielBrosch.github.io/FlagSOS.jl",
        edit_link="main",
        assets=String[],
    ),
    pages=[
        "Home" => "index.md",
        "Examples" => [
            "examples/TriangleFreeGraphs.md",
            "examples/CaccettaHaeggkvist.md",
            "examples/ErrorCorrectingCodes.md"
        ]
    ],
)

deploydocs(;
    repo="github.com/DanielBrosch/FlagSOS.jl",
    devbranch="main",
)
