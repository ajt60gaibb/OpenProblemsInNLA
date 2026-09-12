# IE-21 — Sharp row-deletion singular-value limit for spherical random matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved
**Last checked:** 2026-09-11

<!-- colbrook-recovered -->
## Independently reviewed resolution - 2026-09-11

**Affirmative resolution.** Theorem 1 and Sections 2-5 prove the displayed Gaussian trimmed-second-moment limit in probability along every sequence $`n\to\infty`$ and $`m/n\to\infty`$, with exactly $`\lfloor\theta m\rfloor`$ retained rows and the variational least singular value. Explicit failure-probability and error bounds are included; no faster aspect-ratio growth assumption is added.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](../../references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.pdf), [independent proof review](../../references/colbrook-recovered-2026-09-11/verification/reviews/IE-21-22-review.md), and [submission record](../../references/colbrook-recovered-2026-09-11/README.md). The supplied notes were reconstructed with substantial AI assistance. This is independent agent verification, not external human peer review or formal proof-assistant certification; no novelty or priority claim is made.

The difficulty, importance and rating rationale below are historical assessments of the original open target. Original statements, references and dated audits are preserved.
<!-- /colbrook-recovered -->

**Rating rationale:** Challenging reflects a sharp limit for the least singular value after adversarial row deletion; community impact includes random matrix theory and robust iterative solvers.

## Problem statement

Fix $`0<\theta<1`$. For $`A\in\mathbb R^{m\times n}`$ define

```math
s_\theta(A)=\min_{S\subseteq\{1,\ldots,m\},\ |S|=\lfloor\theta m\rfloor}
\min_{\|x\|_2=1}\|A_Sx\|_2,
```

where $`A_S`$ contains the rows indexed by $`S`$. Let $`a_\theta>0`$ satisfy $`\mathbb P(|G|\le a_\theta)=\theta`$ for $`G\sim N(0,1)`$, and set

```math
h_\theta=\frac1{\sqrt{2\pi}}\int_{-a_\theta}^{a_\theta}t^2e^{-t^2/2}\,dt.
```

For every integer sequence $`(m_j,n_j)`$ with $`n_j\to\infty`$ and $`m_j/n_j\to\infty`$, let the rows of $`A_j\in\mathbb R^{m_j\times n_j}`$ be independent and uniformly distributed on $`\mathbb S^{n_j-1}`$. Is

```math
\frac{s_\theta(A_j)^2}{\|A_j\|_2^2}\ \xrightarrow{\mathbb P}\ h_\theta?
```

This states Steinerberger's proposed asymptotic with $`\theta=q-\beta`$. Convergence in probability and the floor convention make the source's limiting statement explicit. The source also asks for quantitative error bounds; these belong to this problem rather than separate entries.

## Connection to numerical linear algebra

The quantity measures the worst conditioning remaining after rows are discarded. It controls convergence guarantees for quantile Kaczmarz methods on corrupted linear systems.

## References

1. S. Steinerberger, *Quantile-based Random Kaczmarz for corrupted linear systems of equations*, Information and Inference **12**(1) (2023), 448–465, §2.3, equation (8) and the following paragraph. [Published paper](https://doi.org/10.1093/imaiai/iaab029). [Author preprint](https://arxiv.org/abs/2107.05554), v1 (2021), §2.3, equation $`(\diamond)`$.
2. E. Battaglia, J.-F. Cai, J. Chen, A. Ma, D. Needell, and T. Wu, *Quantile Randomized Kaczmarz for Streaming Linear Systems with Massart Noise*, arXiv:2608.27968v1 (2026), §1.1, discussion of Steinerberger's random-matrix heuristic and the distinction between static and streaming data; §5. [Preprint](https://arxiv.org/abs/2608.27968).

## Earlier status check — 2026-09-08

Checked the published formulation and the arXiv version history (2107.05554 has only v1), then searched the problem's title, the author's name with “subsingular”, and combinations of “trimmed/smallest singular value”, “quantile”, “Kaczmarz”, “heuristic”, “proof”, “2025”, and “2026”. The August 2026 streaming paper still describes the original estimate as a heuristic; its fresh-sample convergence bounds do not establish this static-matrix limit. No later proof or counterexample was located in this bounded search. That is a literature-status assessment, not a proof of openness.

## Audit update — 2026-09-10

Rechecked Steinerberger's [primary formulation](https://arxiv.org/pdf/2107.05554), §2.3, and the [2026 streaming follow-up](https://arxiv.org/html/2608.27968v1). Searches found no proof of the static proportional-deletion limit. Cai, Chen, Ma, and Wu's new [subsample-size theorem](https://doi.org/10.1137/25M1785678), SIAM J. Matrix Anal. Appl. 47 (2026), 802–823, concerns quantile estimation during QRK, a different asymptotic quantity.
