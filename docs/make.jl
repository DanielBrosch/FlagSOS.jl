using FlagSOS
using Documenter

DocMeta.setdocmeta!(FlagSOS, :DocTestSetup, :(using FlagSOS); recursive=true)

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
    ],
)

deploydocs(;
    repo="github.com/DanielBrosch/FlagSOS.jl",
    devbranch="main",
)
