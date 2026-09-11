# RA-02 — Polynomial trace-error factor after exactly the target rank of pivots

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because removing exponential loss without oversampling requires sharper adaptive-pivot analysis; community impact is rank-efficient PSD approximation.  
**Topic:** randomized factorization; approximation guarantees  
**Last checked:** 2026-09-11  
**Status:** Solved  

<!-- colbrook-random-pivoting -->
## Resolution — 2026-09-11

**Negative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Theorem 1 and Corollary 3 disprove the existence of constants $C,p$ giving the displayed polynomial bound after exactly $r$ pivots. For every fixed $r\ge1$, real entrywise-positive positive-definite matrices of order $r+1$ approach the sharp expected trace-error ratio $2^r$ as a parameter tends to zero. Choose $r$ first and then the parameter; no limit uniform in $r$ is needed. The result does not address oversampling (RA-01).

[Complete manuscript](../../references/colbrook-random-pivoting-2026-09-11/manuscripts/sharp_random_pivoting.pdf) · [TeX](../../references/colbrook-random-pivoting-2026-09-11/manuscripts/sharp_random_pivoting.tex) · [Independent complete-source PASS review](../../references/colbrook-random-pivoting-2026-09-11/verification/reviews/RA-02-review.md) · [Authorship, exact checks and provenance](../../references/colbrook-random-pivoting-2026-09-11/README.md).

Verification is independent agent review, not external human peer review or formal certification. AI assistance is disclosed; no priority claim is made. The original statement and audits remain below; ratings are historical.
<!-- /colbrook-random-pivoting -->

## Context and notation

For a Hermitian positive-semidefinite $A\in\mathbb C^{n\times n}$, define
the exact-arithmetic RPCholesky residuals by $R_0=A$. Conditional on
$R_t\ne0$, select $j$ with probability $(R_t)_{jj}/\operatorname{tr}(R_t)$
and set

$$
R_{t+1}=R_t-\frac{R_t(:,j)R_t(j,:)}{(R_t)_{jj}}.
$$

If $R_t=0$, keep all subsequent residuals zero. Eigenvalues are ordered
$\lambda_1(A)\geq\cdots\geq\lambda_n(A)\geq0$, and
$\tau_r(A)=\sum_{j>r}\lambda_j(A)$. This is the pivot rule in Chen,
Epperly, Tropp, and Webber, [*Randomly pivoted Cholesky: Practical
approximation of a kernel matrix with few entry evaluations*](https://doi.org/10.1002/cpa.22234),
Algorithm 1; their Lemma 5.5 gives the current comparison
$\mathbb E\operatorname{tr}(R_r)\leq2^r\tau_r(A)$.

## Problem statement

Do constants $C>0$ and $p\geq0$ exist such that, for every $n\geq1$,
every Hermitian positive-semidefinite $A\in\mathbb C^{n\times n}$, and
every integer $1\leq r\leq n$,

$$
\mathbb E\operatorname{tr}(R_r)\leq Cr^p\tau_r(A)?
$$

Both constants must be independent of $n,r,A$. Exactly $r$ RPCholesky
steps are permitted, with the zero-residual convention above. This asks
for a polynomial approximation factor without oversampling; [RA-01](../RA-01/README.md) instead
allows additional pivots to obtain relative error near one.

## References

Epperly, [*Make the Most of What You Have*](https://tropp.caltech.edu/dissertations/Epp25-Making-Most.pdf),
§11.1, Conjecture 11.2, p. 182; Chen et al.,
[RPCholesky](https://doi.org/10.1002/cpa.22234), Lemma 5.5, p. 1020.
Gilles and Wilber, [*Low-Rank Approximation by Randomly Pivoted LU*](https://arxiv.org/html/2601.22344v1),
§3.1, paragraph following Theorem 3, explicitly reiterate this conjecture.

## Source normalization

The dissertation calls $A^{(r)}$ a residual but
prints $\operatorname{tr}(A-A^{(r)})$, without expectation. We use its
cited Lemma 5.5 to correct both notation defects. The later paper confirms
the intended polynomial improvement over that lemma's $2^r$ factor.

## Status check

Searches for `RPCholesky r-step polynomial`,
`RPCholesky conjecture polynomial`, and the cited papers found no resolution.
Epperly's August 2026 oversampling theorem does not supply a polynomial
factor at exactly $r$ steps. Its Theorem 1.2 is noninformative at $k=r$.

## Audit — 2026-09-10

Rechecked [Gilles–Wilber's discussion after Theorem 3](https://arxiv.org/html/2601.22344v1), which reiterates the polynomial-factor conjecture. Exactly-$r$-step and later RPCholesky searches found no resolution. The [August oversampling theorem](https://arxiv.org/html/2608.20633v1) does not establish the displayed factor after exactly $r$ pivots.
