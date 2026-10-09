# TR-26 — Degrees of the two Rayleigh–Ritz discriminant parts for rational normal curves

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** Separating the isotropic and nonisotropic degree contributions requires substantial algebraic analysis beyond the known total. The result mainly interests specialists in conditioning of constrained eigenvalue problems.

<!-- colbrook-unclaimed -->
## Resolution — 2026-09-11

**Affirmative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [The complete proof, Theorem 1 and Sections 2–7](../../references/colbrook-unclaimed-2026-09-11/manuscripts/TR-26.md) proves the reduced isotropic degree $`2d`$ and nonisotropic degree $`6(d-1)`$ for every $`d\ge2`$ in the exact fixed embedding and bilinear model below. It identifies the isotropic hyperplanes, proves irreducibility of the nonisotropic image, and establishes multiplicity one before subtracting degrees. The proof covers infinity, $`d=2`$ and the matrix-to-numerator kernel.

[Manuscript PDF](../../references/colbrook-unclaimed-2026-09-11/manuscripts/TR-26.pdf) · [Independent complete-source PASS review](../../references/colbrook-unclaimed-2026-09-11/verification/reviews/TR-26-review.md) · [Authorship, provenance and submission record](../../references/colbrook-unclaimed-2026-09-11/README.md).

This AI-assisted proof passed independent agent review; this is not external human peer review or formal verification. The difficulty, importance and rating rationale below are historical. The original target and dated status audit are retained. No priority claim is made.
<!-- /colbrook-unclaimed -->

## Problem statement

For every integer $`d\geq2`$, use the specific rational normal curve

```math
C_d=\{[a^d:a^{d-1}b:\cdots:b^d]:[a:b]\in\mathbb P^1\}
\subset\mathbb P^d.
```

For a complex symmetric matrix $`H`$ of order $`d+1`$, consider
$`\rho_H(z)=z^\top Hz/(z^\top z)`$ on the part of $`C_d`$ where $`z^\top z\ne0`$. Transposes here do not conjugate.

Let $`\mathcal R`$ be the Zariski closure in
$`C_d\times\mathbb P(\mathop{\mathrm{Sym}}\nolimits_{d+1}(\mathbb C))`$
of all pairs $`([z],[H])`$ for which $`[z]`$ is a critical point of $`\rho_H|_{C_d}`$. Choose homogeneous generators $`g_i`$ of its ideal and let

```math
\mathcal B=\{([z],[H])\in\mathcal R:
\mathop{\mathrm{rank}}\nolimits(\partial g_i/\partial z_j)\leq d-1\}.
```

Put $`Q=\{([z],[H]):z^\top z=0\}`$ and let $`\pi`$ project to the matrix factor. Define

```math
\Sigma_{\mathrm{iso}}=\pi(\mathcal B\cap Q),\qquad
\Sigma_{\mathrm{noniso}}=\overline{\pi(\mathcal B\setminus Q)}^{\,\mathrm{Zar}}.
```

Are these projective hypersurfaces with

```math
\deg\Sigma_{\mathrm{noniso}}=6(d-1),\qquad
\deg\Sigma_{\mathrm{iso}}=2d?
```

Degree refers to each reduced algebraic set, including all its components. The question is Conjecture 3.14 in the source. Both parts belong to one problem; the standard unweighted embedding and the bilinear quadratic form are fixed.

## Why it matters

These discriminants locate parameter values at which constrained Rayleigh-quotient critical points collide or cease to form a reduced finite set. They describe degeneracy in a basic nonlinear analogue of matrix eigenvalue computations.

## References and status check

1. V. Borovik, H. Friedman, S. Hoşten, and M. Pfeffer, *Numerical Algebraic Geometry for Energy Computations on Tensor Train Varieties*, [arXiv:2512.06939v2](https://arxiv.org/pdf/2512.06939v2), §3.2, Conjecture 3.14, pp.13–14; the correspondence and ramification definitions are on pp.7–13.
2. The same paper, Proposition 3.10, proves the total discriminant degree $`2(4d-3)`$; Examples 3.12–3.13 compute small cases.

### Status check — 2026-09-10

Checked the June 2026 revision, Proposition 3.10, Examples 3.12–3.13 and Conjecture 3.14, and searched the title and rational-normal-curve Rayleigh–Ritz discriminants. Example 3.12 gives an explicit symbolic factorization for $`d=2`$, with isotropic degree four and nonisotropic degree six; this is a proved small-degree case supporting Partially resolved. Example 3.13 also reports symbolic degree computation for $`d=3`$. The separate numerical checks through $`d=10`$ are evidence, not a general proof. The total-degree theorem alone does not determine the component split. No later general proof or counterexample was located.
