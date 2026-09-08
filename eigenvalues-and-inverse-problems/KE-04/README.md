# KE-04 — Strict interlacing across block Lanczos iterations

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** explicit conjecture in a 2025 primary manuscript  
**Last checked:** 2026-09-08

Let $A\in\mathbb R^{n\times n}$ be symmetric and $V\in\mathbb R^{n\times p}$ have full column rank. Write
$$
\mathcal K_j=\operatorname{range}[V,AV,\ldots,A^{j-1}V],
$$
and let $s$ be the largest integer with $\dim\mathcal K_s=sp$. For $1\le j\le s$, choose an orthonormal basis $Q_j$ of $\mathcal K_j$ and order the eigenvalues of $T_j=Q_j^TAQ_j$ as
$\theta_1^{(j)}\le\cdots\le\theta_{jp}^{(j)}$, with multiplicity.

For every $1\le k<j\le s$ and $1\le i\le(k-1)p$, must the open interval
$$
(\theta_i^{(k)},\theta_{i+p}^{(k)})
$$
contain an eigenvalue of $T_j$? The statement concerns exact arithmetic before the first loss of full block dimension. Although Lanczos supplies compatible block tridiagonal representations, the spectra do not depend on the chosen bases.

This would extend a scalar Lanczos property used to interpret later Ritz values and distinguish genuine eigenvalue approximation from clusters created by finite precision.

## References

 D. Šimonová and P. Tichý, *On finite precision block Lanczos computations*, arXiv:2507.16484v1 (22 July 2025), §2.1, unnumbered conjecture and final discussion ([primary manuscript](https://arxiv.org/html/2507.16484v1)). J. Liesen and Z. Strakoš, *Krylov Subspace Methods: Principles and Analysis*, Oxford 2013, the scalar Lanczos/orthogonal-polynomial background cited by the source ([publisher](https://doi.org/10.1093/acprof:oso/9780199655410.001.0001)).

## Status check — 2026-09-08

 The arXiv abstract/history and full §2.1 were inspected; v1 remains the only listed version. Searches “block Lanczos interlacing conjecture”, “Šimonová Tichý interlacing”, and 2026 proof/counterexample queries found no resolution. Standard weak Cauchy interlacing is not the asserted strict interval-occupancy result.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
