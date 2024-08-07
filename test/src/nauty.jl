using FlagSOS
using JET
# using ProfileCanvas
using Profile
# using ProfileView

import .VSCodeServer.view_profile
function view_profile(data = Profile.fetch(); C=false, kwargs...)
    d = Dict{String, VSCodeServer.ProfileFrame}()

    if VERSION >= v"1.8.0-DEV.460"
        threads = ["all", 1:Threads.nthreads()...]
    else
        threads = ["all"]
    end

    if isempty(data)
        Profile.warning_empty()
        return
    end

    lidict = Profile.getdict(unique(data))
    data_u64 = convert(Vector{UInt64}, data)
    for thread in threads
        graph = VSCodeServer.stackframetree(data_u64, lidict; thread=thread, kwargs...)
        d[string(thread)] = VSCodeServer.make_tree(
            VSCodeServer.ProfileFrame(
                "root", "", "", 0, graph.count, missing, 0x0, missing, VSCodeServer.ProfileFrame[]
            ), graph; C=C)
    end

    VSCodeServer.JSONRPC.send(VSCodeServer.conn_endpoint[], VSCodeServer.repl_showprofileresult_notification_type, (; trace=d, typ="Thread"))
end


@time Gs = generateAll(Graph, 6, 1000)
@time Gs = generateAll(Graph, 7, 1000) # 3.2s
@profview Gs = generateAll(Graph, 7, 1000) recur=:flat 
@profview Gs = generateAll(Graph, 7, 1000) format=:flat


@profview_allocs Gs = generateAll(Graph, 7, 1000) recur=:flat


@time Gs = generateAll(Graph, 8, 1000) # 57s
@time Gs = generateAll(Graph, 9, 1000) # 57s

# Profile.clear()
# @profile Gs = generateAll(Graph, 7, 1000)
# view_profile(Profile.fetch(); recur=:flat)
# Profile.print(format=:flat)

# in REPL
@report_opt generateAll(Graph, 3, 1000)
@report_call generateAll(Graph, 5, 1000)

function test(A::Vector{Int})
    push!(A, 1)
end

tmp = [1,2]

tmp2 = FlagSOS.Group()

function test2(G::FlagSOS.Group)
    G.n = 1
end

test2(tmp2)

tmp2.n

function test3(A::Vector{Int})
    A = [1,2,3]
end

tmp = [1,2]
test3(tmp)
tmp