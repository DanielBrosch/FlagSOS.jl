# FlagSOS

[![Stable](https://img.shields.io/badge/docs-stable-blue.svg)](https://DanielBrosch.github.io/FlagSOS.jl/stable/)
[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://DanielBrosch.github.io/FlagSOS.jl/dev/)
[![Build Status](https://github.com/DanielBrosch/FlagSOS.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/DanielBrosch/FlagSOS.jl/actions/workflows/CI.yml?query=branch%3Amain)
[![Coverage](https://codecov.io/gh/DanielBrosch/FlagSOS.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/DanielBrosch/FlagSOS.jl)
[![Aqua](https://raw.githubusercontent.com/JuliaTesting/Aqua.jl/master/badge.svg)](https://github.com/JuliaTesting/Aqua.jl)


A julia package for extremal combinatorics based on the flag algebra method and its variants. The package offers various hierarchies to compute lower bounds for problems of the form

$$
\begin{aligned}
\inf_M\enspace & F(M)\\
\text{s.t. }& G_i(M) \geq 0 \quad\text{ for }i=1,\dots,k,\\
& H_i(M) = 0 \quad\text{ for }i = 1,\dots, \ell,
\end{aligned}
$$

where $F$, $G_i$, $H_i$ are quantum flags (linear combinations of sub-model density functions), and $M$ is a model of fixed size or a converging sequence in a given theory. The constraints can include labels, but then the entire $S_n$ orbit needs to be included.

Check out the [documentation](https://DanielBrosch.github.io/FlagSOS.jl/) for details.

## Citing

See [`CITATION.bib`](CITATION.bib) for the relevant reference(s).
