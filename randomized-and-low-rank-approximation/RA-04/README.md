# RA-04 — Clustered singular-value gaps in randomized block Krylov approximation

**Difficulty:** hard  
**Importance:** interesting to specialist  
**Last checked:** 2026-09-08

**Status:** source-stated conjecture; no resolution found in screening on 2026-09-08.

Let $A\in\mathbb R^{n\times d}$ have singular values $\sigma_1\geq\sigma_2\geq\cdots$. Fix integers $1\leq b\leq k$, set $t=\lceil k/b\rceil$, and set $k'=bt\leq\operatorname{rank}(A)$. Define
$$
\Delta_{k'}^{(b)}=\min_{1\leq i\leq k'-b}
\frac{\sigma_i^2-\sigma_{i+b}^2}{\sigma_i^2},
$$
with the empty minimum set to one, and suppose this gap is positive. Draw $G\in\mathbb R^{n\times b}$ with independent standard Gaussian entries. In exact arithmetic, let $Z$ be an orthonormal basis of
$$
\operatorname{range}[G,(AA^T)G,\ldots,(AA^T)^{q-1}G],
\qquad \widehat A=Z[Z^TA]_k,
$$
where $[B]_k$ denotes a best rank-$k$ approximation obtained by truncating the SVD of $B$.

Does an absolute constant $C$ exist such that, for every such input and every $0<\varepsilon,\delta<1/2$, taking
$$
q=\left\lceil C\left[
\frac{t}{\sqrt\varepsilon}\log\frac{2}{\Delta_{k'}^{(b)}}+
\frac1{\sqrt\varepsilon}\log\frac{n}{\delta\varepsilon}
\right]\right\rceil
$$
gives, with probability at least $1-\delta$, both
$$
\|A-\widehat A\|_\xi\leq(1+\varepsilon)\|A-[A]_k\|_\xi
\quad(\xi=2,F),
$$
and $|\|A v_i\|_2^2-\sigma_i^2|\leq\varepsilon\sigma_{k+1}^2$ for the ordered top $k$ right singular vectors $v_i$ of $\widehat A$? Here $\sigma_{k+1}=0$ if necessary. The factor two makes the logarithm meaningful at a unit gap.

This is the gap-independent algorithmic component of the authors' concluding conjecture. They also conjecture the corresponding improvement in their gap-dependent theorem and random Krylov matrix conditioning theorem; those are not separately counted here. The displayed parameter regime is where the source's spectral-gap expression is finite and defined.

The existing theorem instead depends logarithmically on every consecutive gap and a leading spectral condition number. The proposed bound would explain why a block can accommodate clusters of up to $b$ singular values. It does not ask for a finite-precision extension.

## References

1. T. Chen, E. N. Epperly, R. A. Meyer, C. Musco, and A. Rao, *Does block size matter in randomized block Krylov low-rank approximation?*, arXiv:2508.06486v2. Section 5 states the conjecture; Section 3.3 gives the full quantitative Theorem 1.3, and Algorithm 1 fixes the algorithm. [Paper](https://arxiv.org/html/2508.06486v2).
2. R. A. Meyer, C. Musco, and C. Musco, *On the Unreasonable Effectiveness of Single Vector Krylov Methods for Low-Rank Approximation*, SODA 2024, pp. 811–845, especially Theorem 4.5. [Paper](https://arxiv.org/abs/2305.02535).

## Status check — 2026-09-08

Searched the exact 2025 paper title, “block Krylov b-th order gap conjecture”, and “randomized block Krylov clustered gaps 2026”; checked the current arXiv abstract/version record and Section 5. No proof or counterexample was found. Input perturbation results in Section 3.5 do not establish the unperturbed statement above.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
