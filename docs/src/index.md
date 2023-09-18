```@meta
CurrentModule = FlagSOS
```

# FlagSOS.jl

Documentation for [FlagSOS.jl](https://github.com/DanielBrosch/FlagSOS.jl), a [Julia](https://julialang.org/) package for extremal combinatorics based on the flag algebra method and its variants. The package offers various hierarchies to compute lower bounds for problems of the form

```math
\begin{aligned}
\inf_M\enspace & F(M)\\
\text{s.t. }& G_i(M) \geq 0 \quad\text{ for }i=1,\dots,k,\\
& H_i(M) = 0 \quad\text{ for }i = 1,\dots, \ell,
\end{aligned}
```

where $F$, $G_i$, $H_i$ are quantum flags (linear combinations of sub-model density functions), and $M$ is a model of fixed size or a converging sequence in a given theory. The constraints can include labels, but then the entire $S_n$ orbit needs to be included.

## Examples
- [Basic example: Mantel's theorem](@ref)
- [Constrained example: Caccetta Haeggkvist conjecture](@ref)
- [Finite + high precision example: Error correcting codes](@ref)

## Reference

```@index
```

```@autodocs
Modules = [FlagSOS]
```
