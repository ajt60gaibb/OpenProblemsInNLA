# IE-12 — Near-quadratic solution cost at a prescribed backward error

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** open; removing dimension-dependent overhead from general backward-error solution cost.  
**Last checked:** 2026-09-08  

## Problem statement

Does there exist a randomized algorithm and absolute constants $C,q>0$ such
that, for every $n\ge1$, nonsingular $A\in\mathbb R^{n\times n}$ with
$\|A\|_2=1$, $b\ne0$, and $0<\varepsilon<1/2$, it returns $x\ne0$ satisfying

$$
\Pr\left\{\frac{\|Ax-b\|_2}{\|A\|_2\|x\|_2}
\le\varepsilon\right\}\ge0.99
$$

using at most $C n^2\varepsilon^{-q}$ operations? Use an exact-real arithmetic
model with scalar arithmetic, square roots, comparisons, and independent
standard Gaussian or random-bit draws at unit cost. All input entries may be
accessed; the norm normalization is an input promise. The cost constants must
be independent of the condition number and of $n,b,\varepsilon$.
The fraction is normwise backward error with perturbations allowed in $A$
only. A deterministic algorithm meeting the bound would also answer positively.

## References and status

M. Dereziński, Y. Nakatsukasa, and E. Rebrova,
[*Towards Universal Convergence of Backward Error in Linear System Solvers*](https://arxiv.org/html/2604.16075v2)
(22 May 2026), §§1, 3.1, 5.2, 7, poses the cost question and specifies the
backward-error metric. Corollary 17 gives $O(n^2/\sqrt\varepsilon)$ for PSD
systems. The revised paper's Corollary 25 proves the general-system bound
$O(n^2\log(n/\delta)/\varepsilon)$ with failure probability $\delta$;
its §7 asks for convergence independent of dimension. The remaining target
here removes the $\log n$ overhead, which cannot be hidden in a constant
depending only on $\varepsilon$. The model and success probability above
make this explicit. Searches on 2026-09-08 for “universal backward error 2026
linear systems”, “MINBERR smoothed analysis”, and “quadratic backward error
linear solver” found no resolution of the displayed bound. The earlier
version's lack of a proved general-system rate is no longer current.
