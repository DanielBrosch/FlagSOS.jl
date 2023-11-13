#=
# Non-binary example: symmetric functions

For every choice of $n\in\mathbb{N}$ the symmetric function

$$f = \frac{6-5n+n^2}{n^4}e_2e_2-\frac{2(-3+n)(-1+n)}{n^4}e_1e_3+\frac{2(-1+n)}{n^3} e_4,$$

where $e_i$ denotes the $i$'th elementary symmetric polynomial, is nonnegative on all inputs.
=#

using FlagSOS
using Test #src

n = 10
m = FlagModel{SymmetricFunction, n, Rational{Int}}()

# ## Choosing a relaxation
# As we are not restricting ourselves to binary variables, our only option is the Lasserre-hierarchy:
addLasserreBlock!(m, 4);

# This results in a semidefinite programming problem with block sizes
@test modelSize(m).part == Int[4, 3, 1] #src
modelSize(m)


#=
The package normalizes the bases of the algebra such that the coefficients sum to one. So to get 
```math
e_4 = \sum_{1\leq i<j<k<l\leq n} x_ix_jx_kx_l
```
we need to multiply the element with $\binom{n}{4}$.
=#
e4 = 1//1 * binomial(n, 4) * SymmetricFunction([1, 1, 1, 1])

#=
We need to express $e_1e_3$ in the linear basis of normalized monomial sums:
```math
\begin{aligned}
e_1e_3 &= (x_1+x_2+x_3+x_4+...)(x_1x_2x_3+x_1x_2x_4+...) \\
&= x_1^2x_3x_4+\dots+4x_1x_2x_3x_4+\dots \\
&= m(2,1,1) + 4m(1,1,1,1)
\end{aligned}
```
=#
e1e3 =
    3//1 * binomial(n, 3) * SymmetricFunction([2, 1, 1]) +
    4//1 * binomial(n, 4) * SymmetricFunction([1, 1, 1, 1])

#=
And analogously
```math
\begin{aligned}
e_2e_2&=(x_1x_2+\dots)(x_1x_2+\dots) \\
&= x_1^2x_2^2 +\dots + 2x_1^2x_2x_3 +\dots + 6x_1x_2x_3x_4 + \dots \\
&= m(2,2) + 2m(2,1,1) + 6m(1,1,1,1)
\end{aligned}
```
=#
e2e2 =
    1//1 * binomial(n, 2) * SymmetricFunction([2, 2]) +
    2//1 * 3 * binomial(n, 3) * SymmetricFunction([2, 1, 1]) +
    6//1 * binomial(n, 4) * SymmetricFunction([1, 1, 1, 1])

#=
We now have all the pieces to put together the symmetric function

$$f = \frac{6-5n+n^2}{n^4}e_2e_2-\frac{2(-3+n)(-1+n)}{n^4}e_1e_3+\frac{2(-1+n)}{n^3} e_4.$$
=#
m.objective =
    ((6 - 5 * n + n^2)//n^4) * e2e2 +
    (-(2 * (-3 + n) * (-1 + n)//n^4)) * e1e3 +
    *((2 * (-1 + n))//n^3) * e4

# Finally, we compute the coefficients of the SDP.
computeSDP!(m)

# ## Solving the SDP 
# We solve the relaxation using [Hypatia](https://github.com/chriscoey/Hypatia.jl).
using Hypatia, JuMP
jm = buildJuMPModel(m)
set_optimizer(jm.model, Hypatia.Optimizer)
optimize!(jm.model)
termination_status(jm.model)
#-
objective_value(jm.model)

@test objective_value(jm.model) ≈ 0.0 atol = 7#src
