# IE-06 — The square-root upper bound for Gaussian partial-pivoting growth

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Challenging reflects the need for a sharp probabilistic exponent beyond existing polynomial estimates; community impact is its prediction of typical partial-pivoting stability.

## Context and notation

All elimination in this problem is in exact arithmetic. Write $\|A\|_{\max}=\max_{ij}|a_{ij}|$. A pivoting path creates successive active Schur complements $S_1=A,S_2,\ldots,S_n$, with row/column permutations as appropriate. Its element-growth factor is

$$
\rho(A)=\frac{\max_{1\leq j\leq n}\|S_j\|_{\max}}{\|A\|_{\max}}.
$$

Partial pivoting chooses a largest-magnitude entry in the active first column; complete pivoting chooses one anywhere in the active matrix. If ties occur, a universal statement includes every admissible tie choice; a supremum includes all admissible paths. These conventions remove implementation-dependent ambiguity. Matrices are nonsingular unless otherwise stated.

## Problem statement

Let $G_n\in\mathbb R^{n\times n}$ have independent $N(0,1)$ entries. Is the following precise square-root upper-bound conjecture true?

$$
\text{For every }\eta>0,\qquad
\lim_{n\to\infty}\Pr\{\rho_{\mathrm{PP}}(G_n)>n^{1/2+\eta}\}=0.
$$

Here growth is measured over the exact-arithmetic Schur complements as defined above. This formulation asks only for the conjectured upper exponent; it does not add an unsupported matching lower-bound assertion or a limiting-distribution claim. It is also distinct from [IE-04](../IE-04/README.md), which requires a uniform result after perturbing every deterministic center and prescribes an exponential tail.

## References

Huang and Tikhomirov, [*Average-case analysis of the Gaussian elimination with partial pivoting*](https://doi.org/10.1007/s00440-024-01276-2), PTRF 189 (2024), 501–567, introduction, discussion of Edelman's numerical evidence and main theorems. Trefethen and Schreiber, [*Average-Case Stability of Gaussian Elimination*](https://doi.org/10.1137/0611023), SIAM J. Matrix Anal. Appl. 11 (1990), 335–360.

## Earlier status check — 2026-09-08

Searches for `Gaussian elimination n^{1/2} 2025 2026` and `site:arxiv.org Gaussian growth factor 2026` found polynomial upper bounds and the August worst-case results, but no proof at the square-root exponent. The distinction between exact and computed growth factors matters; the catalog statement fixes the former.

## Audit update — 2026-09-10

The [2024 journal article](https://link.springer.com/article/10.1007/s00440-024-01276-2) distinguishes its proved polynomial bound from the numerically suggested square-root scale. Searches for Gaussian GEPP growth and later work by Huang–Tikhomirov located no proof of the displayed exponent. A polynomial bound with an unspecified larger exponent does not resolve a parameter range of this sharper target.
