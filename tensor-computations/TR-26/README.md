# TR-26 — Degrees of the two Rayleigh–Ritz discriminant parts for rational normal curves

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Separating the isotropic and nonisotropic degree contributions requires substantial algebraic analysis beyond the known total. The result mainly interests specialists in conditioning of constrained eigenvalue problems.

## Problem statement

For every integer $d\geq2$, use the specific rational normal curve
$$
C_d=\{[a^d:a^{d-1}b:\cdots:b^d]:[a:b]\in\mathbb P^1\}
\subset\mathbb P^d.
$$
For a complex symmetric matrix $H$ of order $d+1$, consider
$\rho_H(z)=z^\top Hz/(z^\top z)$ on the part of $C_d$ where $z^\top z\ne0$. Transposes here do not conjugate.

Let $\mathcal R$ be the Zariski closure in
$C_d\times\mathbb P(\operatorname{Sym}_{d+1}(\mathbb C))$
of all pairs $([z],[H])$ for which $[z]$ is a critical point of $\rho_H|_{C_d}$. Choose homogeneous generators $g_i$ of its ideal and let
$$
\mathcal B=\{([z],[H])\in\mathcal R:
\operatorname{rank}(\partial g_i/\partial z_j)\leq d-1\}.
$$
Put $Q=\{([z],[H]):z^\top z=0\}$ and let $\pi$ project to the matrix factor. Define
$$
\Sigma_{\mathrm{iso}}=\pi(\mathcal B\cap Q),\qquad
\Sigma_{\mathrm{noniso}}=\overline{\pi(\mathcal B\setminus Q)}^{\,\mathrm{Zar}}.
$$
Are these projective hypersurfaces with
$$
\deg\Sigma_{\mathrm{noniso}}=6(d-1),\qquad
\deg\Sigma_{\mathrm{iso}}=2d?
$$
Degree refers to each reduced algebraic set, including all its components. The question is Conjecture 3.14 in the source. Both parts belong to one problem; the standard unweighted embedding and the bilinear quadratic form are fixed.

## Why it matters

These discriminants locate parameter values at which constrained Rayleigh-quotient critical points collide or cease to form a reduced finite set. They describe degeneracy in a basic nonlinear analogue of matrix eigenvalue computations.

## References and status check

1. V. Borovik, H. Friedman, S. Hoşten, and M. Pfeffer, *Numerical Algebraic Geometry for Energy Computations on Tensor Train Varieties*, [arXiv:2512.06939v2](https://arxiv.org/pdf/2512.06939v2), §3.2, Conjecture 3.14, pp.13–14; the correspondence and ramification definitions are on pp.7–13.
2. The same paper, Proposition 3.10, proves the total discriminant degree $2(4d-3)$; Examples 3.12–3.13 compute small cases.

### Status check — 2026-09-10

Checked the June 2026 revision, Proposition 3.10, Examples 3.12–3.13 and Conjecture 3.14, and searched the title and rational-normal-curve Rayleigh–Ritz discriminants. Example 3.12 gives an explicit symbolic factorization for $d=2$, with isotropic degree four and nonisotropic degree six; this is a proved small-degree case supporting Partially resolved. Example 3.13 also reports symbolic degree computation for $d=3$. The separate numerical checks through $d=10$ are evidence, not a general proof. The total-degree theorem alone does not determine the component split. No later general proof or counterexample was located.
