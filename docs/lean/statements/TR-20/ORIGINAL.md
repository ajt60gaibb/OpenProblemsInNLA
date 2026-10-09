# TR-20 — Rayleigh–Ritz discriminant degrees for rank-one matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because general discriminant-degree formulas must account for degeneracies and the excluded isotropic locus; specialist importance concerns algebraic conditioning of rank-one Rayleigh–Ritz optimization.  
**Source:** Borovik–Friedman–Hoşten–Pfeffer, Conjecture 3.18 in v2.  
**Last checked:** 2026-09-11  
**Status:** Solved  

<!-- colbrook-recovered-tensors -->
## Resolution — 2026-09-11

**Affirmative resolution by Matthew J. Colbrook**, DAMTP, University of Cambridge. Theorem 1 proves both displayed reduced-degree formulas for every $`n\ge2`$ in the exact complex bilinear Segre model, including boundary and multiplicity analysis.

[Complete proof, Theorem 1 and §§2–8](../../references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-20.pdf) · [TeX](../../references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-20.tex) · [Independent PASS review](../../references/colbrook-recovered-tensors-2026-09-11/verification/reviews/TR-20-review.md) · [Authorship and provenance](../../references/colbrook-recovered-tensors-2026-09-11/README.md).

The AI-assisted proof passed independent agent review, not external human peer review or formal certification. Ratings are historical; no priority claim is made.
<!-- /colbrook-recovered-tensors -->

## Problem statement

For integers $`m,n\ge2`$, put $`N=mn`$ and let

```math
V_{m,n}=\{[\mathop{\mathrm{vec}}\nolimits(ab^T)]:
0\ne a\in\mathbb C^m,\ 0\ne b\in\mathbb C^n\}
\subset\mathbb P^{N-1}.
```

This is the Segre variety of nonzero rank-one $`m\times n`$ matrices modulo scaling, in the ordinary entry coordinates. For a complex symmetric matrix $`H\in\mathbb C^{N\times N}`$ define

```math
R_H([\psi])=\frac{\psi^TH\psi}{\psi^T\psi},
\qquad
[\psi]\in V_{m,n},\quad \psi^T\psi\ne0.
```

Transpose here is bilinear transpose, not conjugate transpose. A critical point is one at which the differential of $`R_H`$ restricted to the smooth variety $`V_{m,n}`$ vanishes. It is degenerate if its Hessian in local coordinates on $`V_{m,n}`$ is singular; at a critical point this condition is independent of the local coordinates.

Let $`\Delta^{\mathrm{ni}}_{m,n}`$ be the Zariski closure in $`\mathbb P(\mathop{\mathrm{Sym}}\nolimits^2\mathbb C^N)`$ of the set of nonzero symmetric matrices $`H`$, modulo scaling, for which such a degenerate critical point exists with $`\psi^T\psi\ne0`$. This is the source's nonisotropic discriminant.

**Conjecture.** For every integer $`n\ge2`$, these discriminants are hypersurfaces and their degrees are  

```math
\deg\Delta^{\mathrm{ni}}_{2,n}
=24\binom{n+1}{3},
\qquad
\deg\Delta^{\mathrm{ni}}_{3,n}
=24n^2\binom n2.
```

Degree means projective degree of the reduced hypersurface, equivalently its intersection number with a general projective line. Both formulas are retained as one source conjecture.

## Why it matters in numerical linear algebra

Minimizing $`R_H`$ over real rank-one matrix states is a constrained energy problem underlying tensor variational algorithms. The discriminant records degeneracies of stationary states, where local solution branches can meet and conditioning can deteriorate. 

## References

1. Viktoriia Borovik, Hannah Friedman, Serkan Hoşten, and Max Pfeffer, [*Numerical Algebraic Geometry for Energy Computations on Tensor Train Varieties*](https://arxiv.org/html/2512.06939v2), arXiv:2512.06939v2 (2026), §3.2, Proposition 3.7, definition before Example 3.11, Conjecture 3.18; §7.2, Table 4.
2. Flavio Salizzoni, Luca Sodomaco, and Julian Weigert, [*Nonlinear Rayleigh quotient optimization*](https://arxiv.org/html/2510.17760v1), 2025, §§2 and 5.

## Status check — 2026-09-10

Rechecked [Borovik et al. v2, Conjecture 3.18 and Table 4](https://arxiv.org/html/2512.06939v2), and searched the title, authors, discriminant and conjecture number. The June 2026 revision retains both formulas as one conjecture. Small-dimensional numerical evidence and generic critical-point counts are not proofs of the stated general discriminant degrees. No later resolution was located.

