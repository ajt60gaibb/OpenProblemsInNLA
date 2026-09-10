# RA-12 — Relative-error threshold for extremal Gaussian trace bounds

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because an explicit threshold must control extremal tails uniformly over spectra; community impact is sharper distribution-level trace-estimation confidence bounds.  
**Source:** Hallman, Conjecture 3 together with Theorem 6.  
**Last checked:** 2026-09-10  
**Status:** Open  

## Problem statement

For a real symmetric $d\times d$ matrix $D$ and integer $m\ge1$, define the Gaussian trace estimator

$$
T_m(D)=\frac1m\sum_{j=1}^{m}z_j^TDz_j,
\qquad z_1,\ldots,z_m\overset{\mathrm{iid}}{\sim}N(0,I_d).
$$

Let $A\ne0$ be any real symmetric positive semidefinite $n\times n$ matrix, with $n\ge1$, and set

$$
\mu=\frac{\operatorname{tr}(A)}{\|A\|_2},\qquad
B_\mu=\frac1\mu\operatorname{diag}
\left(I_{\lfloor\mu\rfloor},\,\mu-\lfloor\mu\rfloor\right).
$$

Here $\|\cdot\|_2$ is the spectral norm, $\mu\ge1$, and a zero final diagonal entry may be retained. Let $X$ have the Gamma distribution with shape and rate both $m\mu/2$. The shape/rate convention means that $\operatorname{Gamma}(\alpha,\beta)$ has density $\beta^\alpha x^{\alpha-1}e^{-\beta x}/\Gamma(\alpha)$ for $x>0$.

**Conjecture.** For every such $A$, every integer $m\ge1$, and every $\varepsilon\ge2/(m\mu)$, the complete comparison chain holds:  
$$
\begin{aligned}
\Pr\!\left(
 |T_m(A)-\operatorname{tr}(A)|
 \ge\varepsilon\operatorname{tr}(A)
\right)
&\le \Pr\!\left(|T_m(B_\mu)-1|\ge\varepsilon\right)\\
&\le \Pr\!\left(|X-1|\ge\varepsilon\right).
\end{aligned}
$$

Each estimator uses Gaussian vectors of its own matrix dimension; only their distributions are compared.

## Why it matters in numerical linear algebra

This would specify the tolerance range on which effective rank yields extremal, distribution-level confidence bounds for Gaussian trace estimation. It also applies to Frobenius-norm estimation through $\|C\|_F^2=\operatorname{tr}(C^TC)$.

## References

1. Eric Hallman, [*Extremal bounds for Gaussian trace estimation*](https://arxiv.org/html/2411.15454v1#S5), arXiv:2411.15454v1 (2024), §5, Theorem 6 and Conjecture 3.
2. Alice Cortinovis and Daniel Kressner, [*On Randomized Trace Estimates for Indefinite Matrices with an Application to Determinants*](https://doi.org/10.1007/s10208-021-09525-9), FoCM 22 (2022), 875–903, Theorem 1.

## Status check

Theorem 6 proves the comparisons beyond an unspecified threshold; Conjecture 3 supplies the explicit threshold above. On 2026-09-08 the [arXiv record](https://arxiv.org/abs/2411.15454) still listed only v1. Title, author, conjecture-number and 2025/2026 searches found no resolution. The author's [later XTrace paper](https://arxiv.org/abs/2512.02316) studies different estimators. This is a bounded check.

## Audit — 2026-09-10

Rechecked [Hallman, Theorem 6 and Conjecture 3](https://arxiv.org/html/2411.15454v1); the record still lists only v1. Author, Gaussian-trace, and conjecture searches found no resolution. An unspecified larger threshold proves a weaker result and does not verify the displayed explicit threshold.
