# RA-03 — Improve the randomized LU squared-error factor to $2^k$

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because nonsymmetric residuals lose the trace identities behind Cholesky bounds; specialist impact is a sharper guarantee for one randomized LU rule.  
**Topic:** randomized LU; low-rank approximation  
**Last checked:** 2026-09-10  
**Status:** Open  

## Problem statement

For $A\in\mathbb C^{m\times n}$, define exact-arithmetic residuals
$S_0=A$. At step $t$, choose $(i,j)$ with conditional probability
$|(S_t)_{ij}|^2/\|S_t\|_F^2$ and update

$$
S_{t+1}=S_t-\frac{S_t(:,j)S_t(i,:)}{(S_t)_{ij}}.
$$

After a zero residual, keep subsequent residuals zero. Prove or refute,
for every $m,n\geq1$, every $A$, and every
$1\leq k\leq\min(m,n)$,

$$
\mathbb E\|S_k\|_F^2\leq2^k
\sum_{j>k}\sigma_j(A)^2,
$$

where singular values decrease with $j$. The bound concerns the mean
squared Frobenius error of this specified algorithm.

## References

Gilles and Wilber, [*Low-Rank Approximation by Randomly
Pivoted LU*](https://arxiv.org/html/2601.22344v1), Algorithm 1 and §3.1,
Theorem 3, Eq. (10), and the following conjecture (pp. 7–8).

## Status check

Their theorem gives $4^k$; the conjecture explicitly
replaces it by $2^k$. Searches for the title, `randomly pivoted LU 2^k`,
and improved RPLU error bounds found no later resolution. The arXiv
submission history listed only v1 of January 29, 2026. The August 2026
RPCholesky theorem addresses a different pivot distribution and norm.

## Audit — 2026-09-10

Rechecked [Algorithm 1, Theorem 3, and the following conjecture](https://arxiv.org/html/2601.22344v1); its record still lists v1. RPLU and improved-bound searches found no resolution. The theorem remains at $4^k$, while the stated squared-error conjecture is $2^k$.
