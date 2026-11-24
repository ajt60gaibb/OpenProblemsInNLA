# IE-07 — Deterministic regularization of the nonsymmetric eigenproblem

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Solved  
**Last checked:** 2026-11-24  

**Rating rationale:** Extreme reflects deterministic regularization of a fully general nonnormal eigenproblem; broad impact comes from replacing randomness in a basic numerical linear algebra primitive.

## Resolution — 2026-11-24

**Solved affirmatively by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Theorem 1.1 (Deterministic spectral regularisation)** of [*Deterministic regularisation of the nonsymmetric eigenproblem*](https://arxiv.org/abs/2611.28614), submitted 21 November 2026, resolves the full original exact-arithmetic target. The proof is in Sections 2–7, with the algorithm, termination, uniform bounds and arithmetic cost assembled in Section 7.

For every $`n\geq2`$, complex contraction $`A`$ and $`0<\delta<1/2`$, the theorem constructs deterministically $`E`$ with $`\|E\|_2<\delta`$ such that $`A+E`$ has simple spectrum and

```math
\frac{\kappa_V(A+E)}{\mathop{\mathrm{gap}}\nolimits(A+E)}
\leq C(n/\delta)^{20/3},
```

using $`O(n^3\log^d(n/\delta))`$ real-field operations and comparisons, for universal $`C,d`$. It also returns an exact eigensystem and inverse eigenbasis. Thus it supplies the required perturbation, including for defective inputs, with $`c=20/3`$ and a strictly stronger perturbation bound. The definitions of the spectral norm, eigenbasis condition number and minimum gap agree with the retained statement below.

The computational model is specified immediately after Theorem 1.1 and in Section 6: arithmetic and comparisons have unit cost, including operations on integers of arbitrary length. The result concerns the exact-arithmetic target; it does not assert a floating-point precision or bit-complexity bound. The status records the cited arXiv result, without asserting a new independent proof audit or Lean verification by this catalog. Section 1.3 discloses AI assistance.

The permanent ID, canonical path, original statement, source references and earlier audit notes are retained. The difficulty and importance ratings are historical; this entry is excluded from the open count.

## Problem statement

For a matrix $`M`$ with simple spectrum, define

```math
\mathop{\mathrm{gap}}\nolimits(M)=\min_{i\ne j}|\lambda_i(M)-\lambda_j(M)|,
\qquad
\kappa_V(M)=\inf_{M=VDV^{-1},\ D\text{ diagonal}}\|V\|_2\|V^{-1}\|_2.
```

For every $`n\geq2`$, $`A\in\mathbb C^{n\times n}`$ with $`\|A\|_2\leq1`$, and $`0<\delta<1/2`$, construct deterministically a matrix $`E`$ such that

```math
\|E\|_2\leq\delta,\qquad A+E\text{ has simple spectrum},\qquad
\frac{\kappa_V(A+E)}{\mathop{\mathrm{gap}}\nolimits(A+E)}\leq C(n/\delta)^c,
```

using $`O(n^3\log^d(n/\delta))`$ exact arithmetic operations, for universal constants $`C,c,d`$. The task is to find the perturbation, not merely prove its existence.

## References

Banks, Garza-Vargas, Kulkarni, and Srivastava, [*Pseudospectral Shattering, the Sign Function, and Diagonalization in Nearly Matrix Multiplication Time*](https://doi.org/10.1007/s10208-022-09577-5), FOCM 23 (2023), §6, first future-research question. Amsel et al., [*Linear Systems and Eigenvalue Problems*](https://arxiv.org/html/2602.05394v3#S3.SS1), August 2026, Problem 3.1.

## Earlier status check — 2026-09-08

Searches for `deterministic pseudospectral shattering 2026` found randomized and exponential-bound deterministic results, not the stated algorithm. The normalization and exponent orientation here are explicit: Problem 3.1's printed $`(\delta/n)^c`$ contradicts its own preceding motivation; $`(n/\delta)^c`$ is the intended polynomial upper bound.

## Audit update — 2026-09-10

Rechecked [workshop version 3](https://arxiv.org/html/2602.05394v3), Problem 3.1. Deterministic pseudospectral-regularization searches found no solution. The corrected reciprocal scale in this entry remains necessary; the source's displayed exponent does not match the intended inverse-polynomial regularity guarantee.
