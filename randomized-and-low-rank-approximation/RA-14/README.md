# RA-14 — Optimal query complexity of spectral rank-$`k`$ approximation

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because matching information bounds for every adaptive algorithm and growing rank is a fundamental barrier; broad impact includes large-scale spectral computation and data analysis.  
**Source:** Bakshi–Narayanan, Open Question 1.10.  
**Last checked:** 2026-09-12  
**Status:** Partially resolved  

## Problem statement

Let $`n\ge2`$, $`1\le k< n`$, and $`0<\varepsilon<1/2`$. An unknown matrix $`A\in\mathbb R^{n\times n}`$ is available through exact products $`Ax`$ and $`A^Tx`$, with one such product counting as one query. An algorithm may choose each real query vector adaptively using all earlier answers and its random bits. Arithmetic and other computation between queries are unrestricted; matrix entries are not otherwise accessible.

Let $`q_{\mathrm{sp}}(n,k,\varepsilon)`$ be the smallest integer $`q`$ for which an algorithm using at most $`q`$ queries returns a matrix $`Z\in\mathbb R^{n\times k}`$ with $`Z^TZ=I_k`$ such that, for every input $`A`$,

```math
\Pr\!\left[
\|A(I-ZZ^T)\|_2
\le (1+\varepsilon)
\min_{\substack{U\in\mathbb R^{n\times k}\\U^TU=I_k}}
\|A(I-UU^T)\|_2
\right]\ge\frac{99}{100}.
```

Probability is over the algorithm's internal randomness, and $`\|\cdot\|_2`$ is the spectral norm.

**Open problem.** Determine $`q_{\mathrm{sp}}(n,k,\varepsilon)`$ up to universal constant factors, with the dependence on $`k`$, $`n`$, and $`\varepsilon`$ simultaneous. In particular, determine the optimal dependence on a growing target rank rather than keeping $`k`$ fixed. The answer must cover the finite-dimensional regime, where learning all columns uses $`n`$ queries.  
This is a square-matrix formulation of the source's question with an editorially fixed two-sided oracle model. The introduction describes products $`Av`$; Algorithm 7.4 explicitly uses both $`A`$ and $`A^T`$. On symmetric inputs these models coincide.

## Why it matters in numerical linear algebra

Matrix products dominate many large-scale singular-subspace computations. The question asks which dependence on the requested number of singular vectors is unavoidable for every adaptive algorithm, rather than for a chosen Krylov implementation.

## References

1. Ainesh Bakshi and Shyam Narayanan, [*Krylov Methods are (nearly) Optimal for Low-Rank Approximation*](https://arxiv.org/html/2304.03191v1#S1.SS2), arXiv:2304.03191v1 (2023), Open Question 1.10; Theorem 1.1 and Algorithm 7.4.
2. Tyler Chen et al., [*Does block size matter in randomized block Krylov low-rank approximation?*](https://arxiv.org/abs/2508.06486), 2025, §1: later block-size bounds.

## Status check

The source's $`O(k\log n/\sqrt\varepsilon)`$ upper bound and fixed-rank lower bound do not determine the growing-rank dependence. The 2025 paper studies Krylov block sizes; its clustered-gap conjecture is separately cataloged.

On 2026-09-08 the [source record](https://arxiv.org/abs/2304.03191) still listed only v1. Searches for “Open Question 1.10,” target-rank matrix-vector complexity, and 2025/2026 follow-ups found no joint characterization. The source's lower bound has a sufficiently-large-dimension regime, not every finite $`n,\varepsilon`$. This is a bounded check.

## Audit — 2026-09-10

Rechecked [Bakshi–Narayanan, Theorem 1.1 and Open Question 1.10](https://arxiv.org/html/2304.03191v1). Fixed-rank spectral complexity is settled in the theorem's sufficiently-large-dimension regime; growing-rank and simultaneous finite-parameter dependence remain unresolved. Later query-complexity searches and the [SODA 2026 block-size paper](https://doi.org/10.1137/1.9781611978971.42) did not settle the full target.


## Further partial results — 12 September 2026

Sidney Holden (Center for Computational Biology, Flatiron Institute, Simons Foundation) supplies [*Bounds and a spectral-to-PCA reduction*](../../references/holden-ra14-2026-09-12/package/report.pdf), Theorems 1.1, 1.2 and 5.1, Sections 2 and 6–8. The [submission record](../../references/holden-ra14-2026-09-12/README.md) includes verified affiliation, source attribution and reproducible checks.

The note proves a universal lower bound of $`k`$ queries, exact $`k`$-query complexity under a rank-at-most-$`k`$ promise, and hence $`q_{\mathrm{sp}}=\Theta(n)`$ when $`k\ge n/2`$, using exact column recovery for the upper bound. A deterministic spectral-to-PCA postprocessor on symmetric inputs satisfying the stated gap promises uses at most $`k\lceil10/\sqrt{\varepsilon}\rceil`$ extra products. Combining this with the cited PCA lower bound yields $`\Theta(k\log n/\sqrt{\varepsilon})`$ when $`n\ge C_*(k/\varepsilon)^D`$ for universal constants. The polynomial dimension restriction is essential and retained; the exponent is not optimized or explicitly evaluated.

A separate [independent informal Codex AI-agent audit](../../references/holden-ra14-2026-09-12/independent-review.md) reviews these partial claims. The simultaneous finite-parameter characterization outside these regimes remains unresolved. **Status remains Partially resolved.** No full solution, external human peer review or formal verification is claimed; no Lean verification was performed.
