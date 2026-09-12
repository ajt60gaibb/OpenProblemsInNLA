# RA-15 — Query complexity from Schatten to spectral norms

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because the information-theoretic transition must be uniform in norm parameter, accuracy, and dimension; community impact is the cost of low-rank approximation across error measures.  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

## Problem statement

For $`1\le p<\infty`$, define the Schatten norm of a real matrix $`M`$ by

```math
\|M\|_{\mathcal S_p}
=\left(\sum_i\sigma_i(M)^p\right)^{1/p},
```

where $`\sigma_i(M)`$ are its singular values; set $`\|M\|_{\mathcal S_\infty}=\max_i\sigma_i(M)`$.

Let $`n\ge2`$, $`p\in[1,\infty]`$, and $`0<\varepsilon<1/2`$. A randomized algorithm accesses an arbitrary unknown $`A\in\mathbb R^{n\times n}`$ only through exact products $`Ax`$ or $`A^Tx`$. Each product costs one query. Query vectors may depend on previous answers and internal randomness; computation between queries is unrestricted.

Define $`q_p(n,\varepsilon)`$ to be the least integer $`q`$ such that some algorithm using at most $`q`$ queries outputs a real unit vector $`v`$ with

```math
\Pr\!\left[
\|A(I-vv^T)\|_{\mathcal S_p}
\le(1+\varepsilon)
\min_{\|u\|_2=1}\|A(I-uu^T)\|_{\mathcal S_p}
\right]\ge\frac{99}{100}
```

for every $`A`$.

**Open problem.** Determine $`q_p(n,\varepsilon)`$ up to universal constant factors simultaneously in $`p`$, $`n`$, and $`\varepsilon`$, including the transition when finite $`p`$ grows with $`n`$ or $`\varepsilon^{-1}`$ and the endpoint $`p=\infty`$. Finite-dimensional saturation must be included, since $`n`$ column queries reveal $`A`$ exactly.  
This square-matrix formulation editorially fixes a two-sided oracle: the source introduction describes $`Av`$, but Algorithm 7.4 uses $`A`$ and $`A^T`$. These models coincide on its symmetric lower-bound inputs. The relative error is in the norm, not its $`p`$th power.

## Why it matters in numerical linear algebra

This asks how the matrix-product cost changes between aggregate singular-value error and worst-direction error.

## References

1. Ainesh Bakshi and Shyam Narayanan, [*Krylov Methods are (nearly) Optimal for Low-Rank Approximation*](https://arxiv.org/html/2304.03191v1#S1.SS2), arXiv:2304.03191v1 (2023), Open Question 1.11; Theorems 1.1 and 1.5, Algorithm 7.4.
2. Praneeth Kacham and David P. Woodruff, [*Faster Algorithms for Schatten-$`p`$ Low Rank Approximation*](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2024.55), APPROX/RANDOM 2024, article 55: later running-time bounds.

## Status check

For fixed finite $`p`$, the source gives a dimension-independent query bound; the spectral lower bound grows with $`\log n`$ in its stated dimension regime. Neither gives optimal uniform dependence on growing $`p`$. The 2024 work improves running time.

Checked 2026-09-08: both arXiv records list only v1. Searches for “Open Question 1.11,” Schatten phase transition, query complexity, and 2025/2026 found no resolution. The older rank-one spectral lower-bound question was solved by the 2023 source. This is a bounded check.

## Audit — 2026-09-10

Rechecked [Bakshi–Narayanan, Theorem 1.1 and Open Question 1.11](https://arxiv.org/html/2304.03191v1). The spectral endpoint has matching bounds in its stated dimension regime; optimal growing-$`p`$ dependence remains open. Later Schatten-query searches found no full characterization; finite-$`p`$ near-optimal results and running-time improvements leave this transition unresolved.
