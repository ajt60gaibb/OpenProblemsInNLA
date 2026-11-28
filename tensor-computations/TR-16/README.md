# TR-16 — Monotonicity of the average number of critical rank-one approximations

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because a dimension comparison of Gaussian critical-point expectations needs control beyond the known integral formula; specialist importance concerns a particular statistic of rank-one approximation landscapes.  
**Last checked:** 2026-11-28

**Status:** Partially resolved

## Statement

For integers $`p\ge3`$ and $`2\le n_1\le\cdots\le n_p`$, let $`G\in\bigotimes_{i=1}^p\mathbb R^{n_i}`$ have independent standard normal entries. Let $`X`$ be the smooth manifold of nonzero real rank-one tensors in this space, and let $`N(G)`$ be the number of critical points on $`X`$ of

```math
Z\longmapsto\|G-Z\|_F^2.
```

Each critical tensor is counted once, regardless of how its vector factors are scaled. Define $`a(n_1,\ldots,n_p)=\mathbb E[N(G)]`$; the critical-point count is finite almost surely.

If

```math
n_p-1>\sum_{i=1}^{p-1}(n_i-1),
```

is it always true that

```math
a(n_1,\ldots,n_{p-1},n_p)
\le a(n_1,\ldots,n_{p-1},n_p-1)?
```

The expectation on the right uses a standard Gaussian tensor in the smaller space.

## Relevance

Rank-one approximation algorithms navigate a landscape of stationary points. This conjecture predicts how the average number of such points changes when one mode becomes much larger than the others.

## References

1. J. Draisma and E. Horobeţ, *The average number of critical rank-one approximations to a tensor*, Linear Multilinear Algebra 64 (2016), 2498–2518. [DOI](https://doi.org/10.1080/03081087.2016.1164660); [primary preprint](https://arxiv.org/pdf/1408.3507), Conjecture 1.3, p.3; §1 defines the Gaussian average and Theorem 1.1 gives an integral formula.
2. S. Friedland and G. Ottaviani, *The Number of Singular Vector Tuples and Uniqueness of Best Rank-One Approximation of Tensors*, Found. Comput. Math. 14 (2014), 1209–1242. [DOI](https://doi.org/10.1007/s10208-014-9194-z); [primary preprint](https://arxiv.org/pdf/1210.8316), Theorem 1, for the corresponding complex critical-point count.

## Status check — 2026-09-10

Rechecked [Draisma–Horobeţ, Conjecture 1.3](https://arxiv.org/pdf/1408.3507), including the direction of the inequality, and searched by the authors, critical-rank-one counts and monotonicity. No proof or counterexample to the real Gaussian statement was located. The matrix case is excluded here, and stabilization of complex critical-point counts does not settle this expectation. No recent explicit primary reaffirmation was found.

## Strict monotonicity on the large $`2\times2\times m`$ slice — 2026-11-28

Carptopus proves $`a(2,2,m)< a(2,2,m-1)`$ for every integer
$`m\ge3\cdot10^{103}+3`$. These comparisons are inside the Gaussian model
and the dimensional threshold of the displayed conjecture. The conclusion
covers this tail of one format family. The comparison between $`m=3`$ and
$`m=4`$, the other values below the proved tail, and other format families
remain open. [Carptopus, Theorem 1.1](https://doi.org/10.5281/zenodo.23353313) ·
[Pinned manuscript](https://github.com/Carptopus/MathExplore-Notes/blob/12ba9e48fd64e6721588b4db4f1972b8af118674/research/effective-eventual-monotonicity-22m-tensor-slice/manuscript.md).

The proof specializes the Draisma–Horobeţ determinant formula to block
sizes $`1,1,m-1`$. Set $`r=m-2`$ and let $`I_r`$ be the expected absolute
determinant of

```math
W-U I_2+\sqrt U\,Z\begin{pmatrix}0&1\\1&0\end{pmatrix},
```

where $`W`$ is the sum of $`r+1`$ independent standard Gaussian rank-one
outer products in dimension two, $`U`$ has the $`\chi_r^2`$ distribution,
and $`Z`$ is standard normal, all independent. Schur complementation and
tilting the scalar normal by $`|t|^{r-1}`$ give
$`a(2,2,m)=\pi I_r/(2r)`$. The normalized determinant expectation has an
Edgeworth expansion $`I_r/r=L+C/r+D/r^2+e_r`$. The verification bounds
$`C>0.0853526992029`$, $`|D|<3753`$ and
$`|e_r|<5.78\cdot10^{49}r^{-5/2}`$ for $`r\ge2^{128}`$. The positive
$`C/r`$ correction then dominates the difference of the other terms
between $`r`$ and $`r+1`$ at the stated threshold.

The audit checked the Gaussian tilt and normalization and replayed the
frozen symbolic expansion, the outward interval bound for $`C`$, and the
arithmetic ledgers for the Fourier remainder and final comparison.
The replay omitted the unused SciPy quadrature import from the shared
symbolic generator. The author identifies those quadrature probes as
numerical controls. [Pinned verification sources](https://github.com/Carptopus/MathExplore-Notes/tree/12ba9e48fd64e6721588b4db4f1972b8af118674/research/effective-eventual-monotonicity-22m-tensor-slice/verification).

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
