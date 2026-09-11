# KE-04 — Strict interlacing across block Lanczos iterations

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solution claimed  
**Last checked:** 2026-09-11  

**Rating rationale:** Challenging reflects a stronger strict interlacing law than general compression interlacing supplies; community impact is spectral information across block Krylov iterations.

## Resolution claim — 2026-09-11

**Affirmative resolution claimed; submitted by Matthew Colbrook.** See the [complete manuscript](solution.md), **Theorem KE-04, sections 1–3** ([PDF](solution.pdf) · [LaTeX](solution.tex)), prepared 11 September 2026.

The manuscript claims strict interval occupancy for every allowed pair of block Lanczos iterations and every indicated index, in exact arithmetic before the first loss of full block dimension. Its quadratic-polynomial argument includes eigenvalue multiplicities and excludes coincident interval endpoints in the stated range.

The manuscript discloses generation in a ChatGPT conversation. Its full proof has not been independently verified here, and no publication or priority claim is made. [Supporting diagnostics](../../references/colbrook-2026-09-11/README.md) were rerun successfully; these are not an independent proof audit. This update checks the submitted claim against the displayed target; the dated literature checks below remain the record of the earlier search. The ratings above are historical, and this entry is excluded from the open count.

## Original problem statement

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

## Audit update — 2026-09-10

Rechecked the explicit conjecture and concluding discussion in the [2025 block-Lanczos manuscript](https://arxiv.org/html/2507.16484v1). Its block-width index ranges agree with this entry. Searches for later strict block-Lanczos interlacing proofs found no resolution; ordinary Cauchy interlacing is weaker than the displayed claim.
