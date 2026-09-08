# TR-04 — Improve the worst-case approximation factor for prescribed tensor-train ranks

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** open; explicit source updated 2026-08-20.  
**Last checked:** 2026-09-08  

## Problem statement

Let $d\ge3$, $n_1,\ldots,n_d\ge2$, and positive integers $r_1,\ldots,r_{d-1}$ be given. Let $S_r\subset\mathbb R^{n_1\times\cdots\times n_d}$ consist of tensors whose unfolding separating modes $1,\ldots,j$ from modes $j+1,\ldots,d$ has rank at most $r_j$, for every $j$. For a dense input tensor $A$, put

$$
E_*(A,r)=\min_{Y\in S_r}\|A-Y\|_F^2.
$$

Find a polynomial-time algorithm returning $X\in S_r$ with

$$
\|A-X\|_F^2<(d-1)E_*(A,r)
\qquad\text{whenever }E_*(A,r)>0,
$$

and exact reconstruction when $E_*(A,r)=0$; alternatively, establish a complexity obstruction to such a guarantee. Ranks may not be increased. Polynomial time is measured in the dense input size and rank parameters, in the idealized arithmetic/SVD model used for TT-SVD; a bit-complexity formulation must additionally specify precision and output tolerances.

This is the tensor-train case of the published tree-network question. The positive-error qualification corrects the impossible strict inequality at zero optimum. It asks for a uniformly valid algorithm, not an empirical improvement or a guarantee restricted to particular input tensors.

## References

I. V. Oseledets, [*Tensor-Train Decomposition*](https://doi.org/10.1137/090752286), *SIAM Journal on Scientific Computing* 33 (2011), 2295–2317, Theorem 2.2 and Corollary 2.4. Amsel et al., [workshop report](https://arxiv.org/html/2602.05394v3), §6.1, Problem 6.1. Matthew Fahrbach and Mehrdad Ghadiri, [*A Tight Lower Bound for the Approximation Guarantee of Higher-Order Singular Value Decomposition*](https://arxiv.org/html/2508.06693v1), Theorems 1.2–1.3, concerns tightness of specific Tucker algorithms rather than a lower bound against all tensor-train algorithms.

## Status check

Searches included `"tensor train" "approximation" "2026" "improvement"` and `"tree tensor" "approximation guarantee" "2026"`. No universal improvement or matching complexity lower bound was located. Randomized methods and better practical error estimates require a separate comparison with the displayed worst-case statement.
