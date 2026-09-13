# The precise remaining problem

This file describes an unresolved mathematical target. None of the proposed extensions below is asserted as a theorem.

Write

```text
x = n/k,  y = x*sqrt(epsilon),  ell = log(e*x).
```

Ignoring only universal multiplicative constants and integer ceilings, the new lower scale and the existing upper scale are

```text
L = n*log(1+y)/y,
U = n*min(1, ell/y).
```

Their ratio is exactly `min(y,ell)/log(1+y)`. As a function of y, it increases until `y=ell` and decreases afterward. The largest gap is therefore of order `ell/log(1+ell)`.

The model test case is

```text
k = 1,
epsilon = (log(n)/n)^2.
```

The new lower bound is `Omega(n*log(log(n))/log(n))`; exact recovery gives the upper bound n. This is not a constant-factor characterization.

## Two sufficient directions, neither established

An all-adaptive lower bound of order

```text
min(n, k/sqrt(epsilon)*log(e*n/k))
```

would match the existing upper bound. Alternatively, a universally valid algorithm with complexity

```text
O(k/sqrt(epsilon)*log(1+n*sqrt(epsilon)/k))
```

would match the new lower bound. A third universally matching expression is also possible. The package does not favor either unproved equality as a conclusion.

## Why the present proof stops at its stated scale

For the tilted Wishart construction, the regularized overlap potential is

```text
Phi = log det(I + (nu/k)*overlap).
```

Its maximum useful scale is `k*log(1+nu/k)`, while its adaptive expected growth is at most a constant times `nu/n` per query in the range used by the proof. The spectral construction chooses `nu` comparable, up to fixed constants and fallbacks, to `n*sqrt(epsilon)` or k. This gives exactly the logarithm `log(1+n*sqrt(epsilon)/k)`.

Simply replacing this logarithm by `log(n/k)` has no justification in the posterior or potential calculation. Using a much larger regularization parameter also increases the available upper bound on per-query growth. The proof does not get the larger logarithm for free.

The warm-start conversion is already charged and its overhead absorbed. Removing that overhead is not the missing unbounded logarithmic factor. The external least-singular-value theorem already applies in the near-square finite-dimensional regime; a deformed-Wigner dimension threshold is no longer the obstacle here.

## Invalid shortcuts to avoid

A deterministic or single-Krylov-start polynomial lower bound does not, without another argument, establish a lower bound against arbitrary adaptive queries. Known block-diagonal hard instances allow one vector query to act in every visible block simultaneously. Exact n-query recovery is an upper bound, not a mechanism for capping or extending a lower bound. Numerical success or failure of selected strategies does not close a universal query-complexity gap.

The current manuscript and claim inventory retain these distinctions. Its newly matched regions should not be confused with a complete RA-14 resolution.
