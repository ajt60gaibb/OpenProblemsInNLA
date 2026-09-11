# PF-01 — Exact positive semidefinite rank of subset-intersection matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because the symmetric subset structure has not yielded matching PSD-rank bounds; specialist importance reflects this explicit family’s role as a benchmark for semidefinite factorization.  
**Status:** Partially resolved  
**Area:** structured positive semidefinite factorization  
**Last checked:** 2026-09-11  

<!-- colbrook-factorization -->
## Partial result — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the stated partial scope.**

The real positive semidefinite rank is exactly four for $n=5$ and $n=6$. Explicit graph factors give the general bound $\operatorname{rank}_{\rm psd}M^{(n)}\le\lceil2\sqrt{2\lfloor(n-1)/2\rfloor}\rceil$, and submatrix monotonicity gives a lower bound of four for every $n\ge5$.

**Remaining question:** The exact ranks as a function of $n$ remain undetermined for $n\ge7$. In particular, the new upper bound five at $n=7,8$ is not accompanied by a matching lower bound five. The finite orders remain part of this single family entry. The ratings assess that surviving question.

**Primary reference:** [complete authored PDF](../../references/colbrook-factorization-2026-09-11/manuscripts/PF-01_subset_intersection.pdf), [standalone TeX](../../references/colbrook-factorization-2026-09-11/manuscripts/PF-01_subset_intersection.tex), **Theorem 1, Corollary 5 and equation (8)**. [Independent proof review](../../references/colbrook-factorization-2026-09-11/verification/reviews/PF-01-review.md) · [Authorship and submission record](../../references/colbrook-factorization-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-factorization -->

## Context and notation

Write $\mathbb S_+^k$ for the cone of real symmetric positive semidefinite $k\times k$ matrices. For an entrywise nonnegative matrix $M\in\mathbb R_+^{p\times q}$, its **real positive semidefinite rank** is

$$
\operatorname{rank}_{\rm psd}(M)
=\min\{k\ge1:\ \exists A_1,\ldots,A_p,B_1,\ldots,B_q\in\mathbb S_+^k,\quad
M_{ij}=\operatorname{tr}(A_iB_j)\ \text{for all }i,j\}.
$$

This definition concerns a family of matrix factors indexed by the rows and columns of $M$.

## Problem statement

For each integer $n\ge5$, let $\mathcal I_n$ and $\mathcal J_n$ consist of the subsets of $\{1,\ldots,n\}$ of cardinalities $\lfloor n/2\rfloor$ and $\lceil n/2\rceil$, respectively. Define the nonnegative matrix

$$
M^{(n)}\in\mathbb R_+^{\mathcal I_n\times\mathcal J_n},
\qquad M^{(n)}_{I,J}=|I\cap J|.
$$

### Question

Determine $\operatorname{rank}_{\rm psd}(M^{(n)})$ exactly as a function of $n$, with real symmetric factors as defined above. The family is one problem; its individual orders are not separate catalog entries.

The source supplies the bounds

$$
\left\lceil\frac{\sqrt{1+8n}-1}{2}\right\rceil
\le \operatorname{rank}_{\rm psd}(M^{(n)})
\le 2\lceil\sqrt n\rceil.
$$

These matrices provide structured benchmarks for algorithms seeking small positive semidefinite factorizations.

## References

Hamza Fawzi, João Gouveia, Pablo A. Parrilo, Richard Z. Robinson, and Rekha R. Thomas, [*Positive semidefinite rank*](https://arxiv.org/html/1407.4095), Mathematical Programming **153** (2015), 133–177, §9.1, Problem 9.2. Arnaud Vandaele, François Glineur, and Nicolas Gillis, [*Algorithms for Positive Semidefinite Factorization*](https://arxiv.org/pdf/1707.07953), Computational Optimization and Applications **71** (2018), 193–219, §4.2, preprint pp. 10–11.

## Status check — 2026-09-10

Rechecked [Fawzi et al., Problem 9.2](https://arxiv.org/html/1407.4095) and [Vandaele–Glineur–Gillis, §4.2](https://arxiv.org/pdf/1707.07953), and searched by subset intersections, Johnson schemes and the problem number. The sources support the displayed real-factor bounds but not an exact formula. No later determination was located; the 2018 algorithm paper remains the latest explicit status source checked, so the later evidence is limited to this search.

