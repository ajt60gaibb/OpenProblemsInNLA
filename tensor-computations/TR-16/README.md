# TR-16 — Monotonicity of the average number of critical rank-one approximations

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because a dimension comparison of Gaussian critical-point expectations needs control beyond the known integral formula; specialist importance concerns a particular statistic of rank-one approximation landscapes.  
**Last checked:** 2026-09-10  
**Status:** Open  

## Statement

For integers $p\ge3$ and $2\le n_1\le\cdots\le n_p$, let $G\in\bigotimes_{i=1}^p\mathbb R^{n_i}$ have independent standard normal entries. Let $X$ be the smooth manifold of nonzero real rank-one tensors in this space, and let $N(G)$ be the number of critical points on $X$ of
$$
Z\longmapsto\|G-Z\|_F^2.
$$
Each critical tensor is counted once, regardless of how its vector factors are scaled. Define $a(n_1,\ldots,n_p)=\mathbb E[N(G)]$; the critical-point count is finite almost surely.

If
$$
n_p-1>\sum_{i=1}^{p-1}(n_i-1),
$$
is it always true that
$$
a(n_1,\ldots,n_{p-1},n_p)
\le a(n_1,\ldots,n_{p-1},n_p-1)?
$$
The expectation on the right uses a standard Gaussian tensor in the smaller space.

## Relevance

Rank-one approximation algorithms navigate a landscape of stationary points. This conjecture predicts how the average number of such points changes when one mode becomes much larger than the others.

## References

1. J. Draisma and E. Horobeţ, *The average number of critical rank-one approximations to a tensor*, Linear Multilinear Algebra 64 (2016), 2498–2518. [DOI](https://doi.org/10.1080/03081087.2016.1164660); [primary preprint](https://arxiv.org/pdf/1408.3507), Conjecture 1.3, p.3; §1 defines the Gaussian average and Theorem 1.1 gives an integral formula.
2. S. Friedland and G. Ottaviani, *The Number of Singular Vector Tuples and Uniqueness of Best Rank-One Approximation of Tensors*, Found. Comput. Math. 14 (2014), 1209–1242. [DOI](https://doi.org/10.1007/s10208-014-9194-z); [primary preprint](https://arxiv.org/pdf/1210.8316), Theorem 1, for the corresponding complex critical-point count.

## Status check — 2026-09-10

Rechecked [Draisma–Horobeţ, Conjecture 1.3](https://arxiv.org/pdf/1408.3507), including the direction of the inequality, and searched by the authors, critical-rank-one counts and monotonicity. No proof or counterexample to the real Gaussian statement was located. The matrix case is excluded here, and stabilization of complex critical-point counts does not settle this expectation. No recent explicit primary reaffirmation was found.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
