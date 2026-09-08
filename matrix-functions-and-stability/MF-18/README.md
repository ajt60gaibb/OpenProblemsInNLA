# MF-18 — Imaginary-part rank in a limiting Green-function matrix equation

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Last checked:** 2026-09-08  
**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** conjecture; no general resolution located as of 2026-09-08  

## Problem statement

Let $n\geq1$, let $C,D,R,P\in\mathbb C^{n\times n}$, and write $M^*$ for conjugate transpose. Suppose $R=R^*$, $P=P^*$, and

$$
P+\lambda D^*+\lambda^{-1}D\succ0
\qquad (|\lambda|=1).
$$

For each $\eta>0$, let $X_\eta$ be the unique nonsingular solution of

$$
X_\eta+(C^*+i\eta D^*)X_\eta^{-1}(C+i\eta D)
 =R+i\eta P
$$

satisfying $\rho(X_\eta^{-1}(C+i\eta D))<1$, where $\rho$ denotes spectral radius. Assume the finite limit $X_0=\lim_{\eta\downarrow0}X_\eta$ exists and is nonsingular. Assume the matrix polynomial

$$
\mathcal P_0(\lambda)=\lambda^2C^*-\lambda R+C
$$

is regular, meaning $\det\mathcal P_0(\lambda)\not\equiv0$. Suppose its eigenvalues on the unit circle are all simple (algebraic multiplicity one). Their number is even; denote it by $2m$.

Is it always true that

$$
\operatorname{rank}\!\left(\frac{X_0-X_0^*}{2i}\right)=m?
$$

## Why this matters for NLA

The rank describes the non-Hermitian part of the selected matrix-equation solution in Green-function computations. It connects a limiting nonlinear solve to the spectrum of a structured quadratic polynomial.

The source proves the upper bound by $m$. Its earlier SIAM paper proves equality for real $C,R$, $P=I$, $D=0$; the general complex case remains the question. Existence of the limit is assumed, not conjectured here.

## References

1. C.-H. Guo, Y.-C. Kuo, W.-W. Lin, [*Numerical solution of nonlinear matrix equations arising from Green's function calculations in nano research*](https://doi.org/10.1016/j.cam.2012.05.012), JCAM 236 (2012), 4166–4180: equation (1), Theorems 3 and 5, and the conjecture on p. 4172. [Author manuscript](https://uregina.ca/~chguo/JCAM_GuoKuoLin.pdf): pp. 1, 5–8.
2. The same authors, [*On a nonlinear matrix equation arising in nano research*](https://doi.org/10.1137/100814706), SIMAX 33 (2012), 235–262, §3: the real-coefficient case.

## Status check

On 2026-09-08, checked both papers' scope and Guo's [publication list through 2026](https://uregina.ca/~chguo/paper.html). Searches using the JCAM title, authors, “Green rank conjecture,” “weakly stabilizing,” and 2025/2026 found no general resolution. The source proves only the upper bound in the stated complex setting. This is a bounded literature check.
