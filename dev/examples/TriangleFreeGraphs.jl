using FlagSOS
using Hypatia, JuMP

edge = Graph(Bool[0 1; 1 0])
triangle = Graph(Bool[0 1 1; 1 0 1; 1 1 0])

m = FlagModel{Graph}()
addForbiddenFlag(m, triangle)
addLasserreBlock!(m, 5)
@show modelSize(m)

m.objective = -1*edge
computeSDP!(m)

jm = buildJuMPModel(m)
set_optimizer(jm.model, Hypatia.Optimizer)
optimize!(jm.model)
@show termination_status(jm.model)
@show objective_value(jm.model)
@show primal_feasibility_report(jm.model)

@test objective_value(jm.model) ≈ 0.5 #src