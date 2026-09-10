# RA-13 — Absolute-error threshold for extremal Gaussian trace bounds

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because signed eigenvalue contributions require uniform extremal tail comparisons; community impact is rigorous trace estimates for indefinite matrices.  
**Last checked:** 2026-09-10  
**Status:** Open  

## Problem statement

For a real symmetric $d\times d$ matrix $D$, define

$$
T_m(D)=\frac1m\sum_{j=1}^{m}z_j^TDz_j,
\qquad z_1,\ldots,z_m\overset{\mathrm{iid}}{\sim}N(0,I_d).
$$

Let $A\ne0$ be an arbitrary real symmetric $n\times n$ matrix, possibly indefinite. Put

$$
\lambda=\|A\|_2,\qquad
\phi=\|A\|_F,\qquad
\rho=\frac{\phi^2}{\lambda^2},\qquad
B_{\lambda,\phi}
=\lambda\operatorname{diag}\left(
I_{\lfloor\rho\rfloor},\sqrt{\rho-\lfloor\rho\rfloor}
\right).
$$

The norms are the spectral and Frobenius norms. Let $X$ have Gamma shape $m\rho/2$ and rate $m/(2\lambda)$, so that $\mathbb E X=\phi^2/\lambda$. Here a Gamma variable with shape $\alpha$ and rate $\beta$ has density $\beta^\alpha x^{\alpha-1}e^{-\beta x}/\Gamma(\alpha)$ for $x>0$.

**Conjecture.** For every integer $n\ge1$, every such $A$, every integer $m\ge1$, and every  
$$
\varepsilon\ge
\frac{2\lambda}{m}
+\sqrt{\frac{2\phi^2}{m}
+\left(\frac{2\lambda}{m}\right)^2},
$$

the following comparisons hold:

$$
\begin{aligned}
\Pr\!\left(|T_m(A)-\operatorname{tr}(A)|\ge\varepsilon\right)
&\le
2\Pr\!\left(T_m(B_{\lambda,\phi})
-\operatorname{tr}(B_{\lambda,\phi})\ge\varepsilon\right)\\
&\le 2\Pr\!\left(X-\frac{\phi^2}{\lambda}\ge\varepsilon\right).
\end{aligned}
$$

Zero trailing diagonal entries in $B_{\lambda,\phi}$ are harmless. Each probability uses the appropriate estimator dimension. This is an absolute-error question, even when $\operatorname{tr}(A)=0$.

## Why it matters in numerical linear algebra

The bound would quantify trace-estimation error even when positive and negative eigenvalues cancel.

## References

1. Eric Hallman, [*Extremal bounds for Gaussian trace estimation*](https://arxiv.org/html/2411.15454v1#S5), arXiv:2411.15454v1 (2024), §5, Theorem 7 and Conjecture 4.

## Status check

Theorem 7 leaves its threshold unspecified. Checked 2026-09-08: the source still lists only v1. Author, title and 2025/2026 searches, including the [later XTrace paper](https://arxiv.org/abs/2512.02316), found no resolution. This is a bounded check.

The displayed conjecture is retained despite a source prose inconsistency: its threshold tends to zero as $m\to\infty$, whereas the following sentence says it tends to $\phi$.

## Audit — 2026-09-10

Rechecked [Hallman, Theorem 7 and Conjecture 4](https://arxiv.org/html/2411.15454v1); the record remains v1. Author and extremal-Gaussian-trace searches found no resolution. The displayed formula matches the numbered conjecture; its inconsistent following prose remains disclosed, and no sharper threshold is claimed proved.
