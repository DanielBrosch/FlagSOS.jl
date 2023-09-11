# For finite n and variable n flag algebras

using AbstractAlgebra

R, pN = PolynomialRing(qq, "n")

# Calculates binom(f,a), where f is a polynomial, and k an integer
function binCoeffPoly(f, k, fact = false)
    if k == 0
        return 1 // 1
    end
    if fact
        return prod([f + 1 - i for i = 1:k]) .* 1 // factorial(k)
    else
        tmp = f
        for i = 2:k
            tmp *= f + 1 - i
        end
        return tmp
    end
end

# Calculate the number of ways [n] can be split into partition (n-sum lambda, lambda)
function numSplits(p, total = pN)
    if length(p) == 0
        return 1
    end
    tmpB = 1
    for k = 1:length(p)
        tmpB *= factorial(p[k])
    end
    tmpA = 1 // tmpB
    shift = 0
    for k = 1:length(p)

        tmpA *= binCoeffPoly(total - shift, p[k], false)
        shift += p[k]
    end
    return tmpA #.*1// tmpB
end

# Calculates all vectors entrywise at most p with sum k
function allSmallerPartsOfSizeUpTo(p, k, exact = false)
    res = []
    if length(p) == 0
        return [[]]
    end
    for i = 0:min(p[1], k)
        if i == k || ((!exact) && length(p) == 1)
            push!(res, vcat([i], repeat([0], length(p) - 1)))
        elseif !exact || sum(p[2:end]) >= k - i
            tmp = allSmallerPartsOfSizeUpTo(p[2:end], k - i, exact)
            for p2 in tmp
                push!(res, vcat([i], p2))
            end
        end
    end
    return res
end


"""
    overlaps(lambda, mu [, total = pN, limit::Bool = false, fixedN = false])

Calculate the different ways two partitions can overlap, with multiplicities. Lambda is considered fixed, mu changes. Adds a biggest dynamic part by (lambda,n-sum(lambda)). Result is array of pairs, first is multiplicity depending on n, second is matrix. Rows are lambda i (last is dynamic sized), columns are mu i (last is dynamic sized)

To get the total amount of combinations (i.e. lambda can move around, too), multiply all multiplicities with numSplits(lambda). We have overlaps(lambda,mu) * numsplits(lambda) == overlaps(mu,lambda) * numSplits(mu).
# Examples
```julia-repl
julia> overlaps([1],[2])
2-element Array{Any,1}:
 (1//2*n^2-3//2*n+1//1, [0 2; 1 0])
 (n-1//1, [1 1; 0 0])
```
Corresponds to the two ways the partitions (1,n-1) and (2,n-2) can overlap. The first element is the overlap, where the 2-part of mu lies in the n-1 part of lambda, with multiplicity n-1 choose 2. The second is the one where 1 element of the 2-part of mu lies in the 1-part of lambda, with multiplicity n-1 choose 1.
"""
function overlaps(
    lambda::AbstractVector,
    mu::AbstractVector,
    total = pN,
    limit::Bool = false,
    fixedN::Bool = false,
)

    res = []

    if fixedN && total < sum(mu; init = 0)
        return res
    end

    l1 = length(lambda) > 0 ? lambda[1] : 0

    options = []
    if limit
        options = [[0 for i = 1:length(mu)]]
    else
        options = allSmallerPartsOfSizeUpTo(mu, l1)
    end

    for p in options
        rest = l1 - (length(p) > 0 ? sum(p) : 0)
        diff = mu .- p
        multiplicity = numSplits(p, l1)#*total^0 #diff) * n^0
        if length(lambda) > 1
            for ov in overlaps(lambda[2:end], diff, total - l1, limit, fixedN)
                push!(res, (ov[1] * multiplicity, hcat(vcat(p, [rest]), ov[2])))
            end
        elseif length(diff) > 0 && sum(diff) > 0
            if (!fixedN) || total - l1 >= sum(diff)
                tmp = hcat(vcat(p, [rest]), vcat(diff, [0]))
                push!(res, (multiplicity * numSplits(diff, total - l1), tmp))
            end
        else
            push!(
                res,
                (multiplicity, hcat(vcat(p, [rest]), vcat(repeat([0], length(p) + 1)))),
            )

        end
    end
    return res
end