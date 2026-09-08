# TR-20 — Rayleigh–Ritz discriminant degrees for rank-one matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Source:** Borovik–Friedman–Hoşten–Pfeffer, Conjecture 3.18 in v2.  
**Last checked:** 2026-09-08  

## Problem statement

For integers $m,n\ge2$, put $N=mn$ and let

$$
V_{m,n}=\{[\operatorname{vec}(ab^T)]:
0\ne a\in\mathbb C^m,\ 0\ne b\in\mathbb C^n\}
\subset\mathbb P^{N-1}.
$$

This is the Segre variety of nonzero rank-one $m\times n$ matrices modulo scaling, in the ordinary entry coordinates. For a complex symmetric matrix $H\in\mathbb C^{N\times N}$ define

$$
R_H([\psi])=\frac{\psi^TH\psi}{\psi^T\psi},
\qquad
[\psi]\in V_{m,n},\quad \psi^T\psi\ne0.
$$

Transpose here is bilinear transpose, not conjugate transpose. A critical point is one at which the differential of $R_H$ restricted to the smooth variety $V_{m,n}$ vanishes. It is degenerate if its Hessian in local coordinates on $V_{m,n}$ is singular; at a critical point this condition is independent of the local coordinates.

Let $\Delta^{\mathrm{ni}}_{m,n}$ be the Zariski closure in $\mathbb P(\operatorname{Sym}^2\mathbb C^N)$ of the set of nonzero symmetric matrices $H$, modulo scaling, for which such a degenerate critical point exists with $\psi^T\psi\ne0$. This is the source's nonisotropic discriminant.

**Conjecture.** For every integer $n\ge2$, these discriminants are hypersurfaces and their degrees are  
$$
\deg\Delta^{\mathrm{ni}}_{2,n}
=24\binom{n+1}{3},
\qquad
\deg\Delta^{\mathrm{ni}}_{3,n}
=24n^2\binom n2.
$$

Degree means projective degree of the reduced hypersurface, equivalently its intersection number with a general projective line. Both formulas are retained as one source conjecture.

## Why it matters in numerical linear algebra

Minimizing $R_H$ over real rank-one matrix states is a constrained energy problem underlying tensor variational algorithms. The discriminant records degeneracies of stationary states, where local solution branches can meet and conditioning can deteriorate. 

## References

1. Viktoriia Borovik, Hannah Friedman, Serkan Hoşten, and Max Pfeffer, [*Numerical Algebraic Geometry for Energy Computations on Tensor Train Varieties*](https://arxiv.org/html/2512.06939v2), arXiv:2512.06939v2 (2026), §3.2, Proposition 3.7, definition before Example 3.11, Conjecture 3.18; §7.2, Table 4.
2. Flavio Salizzoni, Luca Sodomaco, and Julian Weigert, [*Nonlinear Rayleigh quotient optimization*](https://arxiv.org/html/2510.17760v1), 2025, §§2 and 5.

## Status check

The current v2, submitted 2026-06-18, retains Conjecture 3.18. Table 4 gives small-dimensional numerical evidence, not a general proof. On 2026-09-08, exact-title, author, discriminant and conjecture-number searches found no resolution. Known generic critical-point counts are different invariants. This is a bounded check.
