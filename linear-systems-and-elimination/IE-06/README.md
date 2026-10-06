# IE-06 — The square-root upper bound for Gaussian partial-pivoting growth

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved
**Last checked:** 2026-10-06

## Resolution — 2026-10-06

**Conjecture origin:** The conjecture goes back to Lloyd N. Trefethen and David Bau III, *Numerical Linear Algebra* (SIAM, 1997), p. 169.

**Affirmative resolution; not Lean verified.** John Urschel's [*On the Growth Factor of Random Matrices*](https://arxiv.org/abs/2610.06785v1), posted 5 October 2026, resolves the square-root upper-bound target below: see **Theorem 1.4**, together with **Section 5.1 and the proof of Proposition 5.1** for growth over all Schur complements. The original problem statement and permanent ID are retained.

The status is recorded as **Solved** on the basis of this arXiv preprint. This update checks the source's correspondence with IE-06; it is not an independent audit of the full proof. No Lean verification is recorded.

The difficulty, importance and rating rationale are historical assessments of the original open target.

**Rating rationale:** Challenging reflects the need for a sharp probabilistic exponent beyond existing polynomial estimates; community impact is its prediction of typical partial-pivoting stability.

## Context and notation

All elimination in this problem is in exact arithmetic. Write $`\|A\|_{\max}=\max_{ij}|a_{ij}|`$. A pivoting path creates successive active Schur complements $`S_1=A,S_2,\ldots,S_n`$, with row/column permutations as appropriate. Its element-growth factor is

```math
\rho(A)=\frac{\max_{1\leq j\leq n}\|S_j\|_{\max}}{\|A\|_{\max}}.
```

Partial pivoting chooses a largest-magnitude entry in the active first column; complete pivoting chooses one anywhere in the active matrix. If ties occur, a universal statement includes every admissible tie choice; a supremum includes all admissible paths. These conventions remove implementation-dependent ambiguity. Matrices are nonsingular unless otherwise stated.

## Problem statement

Let $`G_n\in\mathbb R^{n\times n}`$ have independent $`N(0,1)`$ entries. Is the following precise square-root upper-bound conjecture true?

```math
\text{For every }\eta>0,\qquad
\lim_{n\to\infty}\Pr\{\rho_{\mathrm{PP}}(G_n)>n^{1/2+\eta}\}=0.
```

Here growth is measured over the exact-arithmetic Schur complements as defined above. This formulation asks only for the conjectured upper exponent; it does not add an unsupported matching lower-bound assertion or a limiting-distribution claim. It is also distinct from [IE-04](../IE-04/README.md), which requires a uniform result after perturbing every deterministic center and prescribes an exponential tail.

## Scope of the resolution

For every $`\alpha>0`$, Urschel's Theorem 1.4 gives constants $`C_\alpha,n_\alpha`$ such that, for $`n\ge n_\alpha`$,

```math
\Pr\!\left\{\mathrm{growth}(\Pi(G_n))>
\sqrt n\,e^{C_\alpha\sqrt{\log n}}\right\}< n^{-\alpha}.
```

Here $`\Pi`$ applies partial pivoting and the paper defines $`\mathrm{growth}`$ using $`L`$ and $`U`$. [Section 5.1](https://arxiv.org/html/2610.06785v1#S5.SS1) and the [proof of Proposition 5.1](https://arxiv.org/html/2610.06785v1#S5.SS2) explicitly control every Schur-complement entry. Since $`\|G_n\|_{\max}\ge1`$ except with exponentially small probability, that argument also bounds the retained $`\rho_{\mathrm{PP}}`$ at the same scale. For each fixed $`\eta>0`$, $`e^{C_\alpha\sqrt{\log n}}=o(n^\eta)`$, implying the displayed limit. The Gaussian model and exact-arithmetic assumptions agree; pivot ties have probability zero.

Lloyd N. Trefethen's [*Instability of Gaussian elimination is exponentially rare (proof of partial result)*](https://arxiv.org/abs/2610.04761v1), posted 3 October 2026, treats the corner entry $`u_{nn}`$. In the correspondence supplied for this update, Trefethen dates that proof to 2015 and says he has not checked Urschel's proof. Credit for the conjecture remains with Trefethen, including its appearance in Trefethen and Bau's *Numerical Linear Algebra* (1997), p. 169; the full resolution is due to Urschel.

## References

John Urschel, [*On the Growth Factor of Random Matrices*](https://arxiv.org/abs/2610.06785v1), arXiv:2610.06785v1 (5 October 2026), Theorem 1.4, Section 5.1 and Proposition 5.1. Lloyd N. Trefethen, [*Instability of Gaussian elimination is exponentially rare (proof of partial result)*](https://arxiv.org/abs/2610.04761v1), arXiv:2610.04761v1 (3 October 2026). Lloyd N. Trefethen and David Bau III, *Numerical Linear Algebra*, SIAM (1997), p. 169.

Huang and Tikhomirov, [*Average-case analysis of the Gaussian elimination with partial pivoting*](https://doi.org/10.1007/s00440-024-01276-2), PTRF 189 (2024), 501–567, introduction, discussion of Edelman's numerical evidence and main theorems. Trefethen and Schreiber, [*Average-Case Stability of Gaussian Elimination*](https://doi.org/10.1137/0611023), SIAM J. Matrix Anal. Appl. 11 (1990), 335–360.

## Earlier status check — 2026-09-08

Searches for `Gaussian elimination n^{1/2} 2025 2026` and `site:arxiv.org Gaussian growth factor 2026` found polynomial upper bounds and the August worst-case results, but no proof at the square-root exponent. The distinction between exact and computed growth factors matters; the catalog statement fixes the former.

## Audit update — 2026-09-10

The [2024 journal article](https://link.springer.com/article/10.1007/s00440-024-01276-2) distinguishes its proved polynomial bound from the numerically suggested square-root scale. Searches for Gaussian GEPP growth and later work by Huang–Tikhomirov located no proof of the displayed exponent. A polynomial bound with an unspecified larger exponent does not resolve a parameter range of this sharper target.
