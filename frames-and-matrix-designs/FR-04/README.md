# FR-04 — Universal exponential deterioration of minimally redundant real phase-retrieval frames

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-11

**Rating rationale:** A universal bound over every full-spark measurement design requires a structural obstruction beyond the Gaussian analysis; it matters for stable phase retrieval.


<!-- colbrook-frames -->
## Reviewed submission - 2026-09-11

Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge.

Theorems 1 and 3 prove a sharp weighted planar inequality and the general bound $\omega_n(A)\le\sqrt{4\|A\|_F^2/(nM)}\sin(\pi/(2M))$, $M=m-n+2$. For $m=2n-1$ this is $O(L(A)n^{-3/2})$. The polynomial order was already known; this self-contained weighted argument does not establish exponential deterioration. The displayed conjecture remains Open.

See the [manuscript](../../references/colbrook-frames-2026-09-11/manuscripts/planar_projection_bound.pdf), [independent agent review](../../references/colbrook-frames-2026-09-11/verification/reviews/FR-04-review.md), and [reproducible submission record](../../references/colbrook-frames-2026-09-11/README.md). Independent agent review is not external human peer review or formal proof-assistant certification. Original problem, ratings and historical audits are retained below.
<!-- /colbrook-frames -->

For $n\geq2$, let $A\in\mathbb R^{(2n-1)\times n}$ be full spark: every choice of $n$ rows is linearly independent. Write $a_i^T$ for its rows and define
$$
L(A)=\max_{1\leq i\leq2n-1}\|a_i\|_2,\qquad
\omega(A)=\min_{\substack{T\subseteq\{1,\ldots,2n-1\}\\|T|=n}}
\sigma_{\min}(A_T).
$$
Do absolute constants $C>0$ and $0<\beta<1$ exist such that
$$
\omega(A)\leq C L(A)\beta^n
$$
for every $n\geq2$ and every such $A$?

For a full-spark matrix at this row count, the displayed definition is equivalent to the Balan–Wang definition taking the minimum over row sets whose complements fail to span $\mathbb R^n$. It measures a worst-conditioned square subproblem in inversion of the phaseless map $x\mapsto |Ax|$. The conjecture says that clever deterministic measurement design cannot avoid exponential deterioration at minimal real redundancy.

## References

1. R. Balan and Y. Wang, *Invertibility and robustness of phaseless reconstruction*, Applied and Computational Harmonic Analysis 38 (2015), pp. 469–488. Conjecture 5.1 on printed p. 484; definitions and stability comparisons in Sections 3–5. [Author-hosted paper](https://www.cscamm.umd.edu/publications/ACHA2015paper_CS-16-05.pdf).
2. A. S. Bandeira et al., *Randomstrasse 101: Open Problems of 2025*, arXiv:2603.29571 (2026), Conjecture 20. [Paper](https://arxiv.org/html/2603.29571v1).
3. Y. Shmalo, *Extreme least singular values of Gaussian row submatrices and a phase retrieval stability problem*, arXiv:2607.06249 (2026). Abstract and Section 1.2/Corollary 1.2 give the critical real Gaussian asymptotic. [Paper](https://arxiv.org/abs/2607.06249).

## Status check — 2026-09-10

Searched “Balan Wang exponential conjecture solved”, “phase retrieval stability omega 2026”, and checked the latest abstract of arXiv:2607.06249. The July 2026 result proves $\omega(A_n)=4^{-n+o_P(n)}$ for independent standard Gaussian entries. A probabilistic result for this ensemble does not prove the uniform inequality over all full-spark matrices. The separate Gaussian-base question should therefore be excluded, while this deterministic conjecture remains open in the screened literature.

**Audit update (2026-09-10):** Rechecked Conjecture 20 and Shmalo’s July 2026 Gaussian asymptotic, then searched for universal Balan–Wang bounds. A high-probability ensemble theorem is not a deterministic bound for every full-spark matrix, so the target remains open. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
