# RA-01 — Optimal pivot count for RPCholesky trace approximation

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** randomized low-rank approximation; kernel matrices  
**Last checked:** 2026-09-08  
**Status:** open; admitted after a bounded literature search found no resolution.  

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

Does there exist a universal constant $C\geq1$ such that, for every
$n\geq1$, every Hermitian positive-semidefinite $A\in\mathbb C^{n\times n}$,
every integer $1\leq r\leq n$, and every $0<\varepsilon<1$, RPCholesky
satisfies

$$
\mathbb E\operatorname{tr}(R_k)\leq(1+\varepsilon)\tau_r(A),
\qquad k=\min\{n,\lceil Cr/\varepsilon\rceil\}?
$$

The expectation is over the algorithm's adaptive pivots. The constant must
be independent of dimension, spectrum, rank, and tolerance. The target
concerns this fixed pivoting rule.

## References

Epperly, [*A new analysis of the randomly pivoted Cholesky
algorithm*](https://arxiv.org/html/2608.20633v1), §1.2, conjecture immediately
after Eq. (1.5), and Corollary 1.3. Earlier motivation appears in
Epperly, [*Make the Most of What You Have*](https://tropp.caltech.edu/dissertations/Epp25-Making-Most.pdf),
Caltech dissertation (2025), §11.1, p. 181.

## Status check

The August 2026 paper proves the larger bound
$k\geq r/\varepsilon+2r\sqrt{\log r}+r\log(1/\varepsilon)+2.3r$
and explicitly conjectures the displayed improvement. Searches for the
paper's title, `RPCholesky optimal r epsilon`, and `RPCholesky conjecture`
found no subsequent resolution. The arXiv record listed only v1, posted
August 21, 2026. The weaker dissertation Conjecture 11.1 is therefore
excluded as resolved by this later preprint.
