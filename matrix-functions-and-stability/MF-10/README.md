# MF-10 — Algebraicity of joint spectral radii from rational input

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because exact arithmetic character of rational-input growth rates remains a longstanding barrier; community impact concerns representability and certification of spectral computations.  
**Status:** Partially resolved  
**Last checked:** 2026-11-28  

## Context and notation

The joint spectral radius of a nonempty compact set $`\mathcal M\subset\mathbb C^{d\times d}`$ is

```math
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
```

This definition also applies to finite real matrix sets. The ordinary spectral
radius of one matrix is written $`\rho(A)`$.

## Problem statement

Is it true that, for every $`d\ge1`$ and every finite nonempty
$`\mathcal M\subset\mathbb Q^{d\times d}`$, there exists a nonzero polynomial
$`p\in\mathbb Z[t]`$ such that

```math
p\bigl(\widehat\rho(\mathcal M)\bigr)=0?
```

The claim is about the value being algebraic; it does not assert a uniform
procedure for finding its minimal polynomial.

## Reference and status evidence

The [finite common-range reduction](../MF-09/common-range-reduction.md#algebraicity-consequence)
proves algebraicity when a rational family is split into a subfamily with
algebraic joint spectral radius and generators whose images lie in a common
rational subspace, and all maps obtained by returning to that subspace are
simultaneously triangularizable or simultaneously similar to normal
matrices. If the full growth rate exceeds that of the first subfamily,
one finite word attains it. The range dimension and matrix ranks need
not be one. This gives an exact subclass. Algebraicity for unrestricted
rational families remains open.

Jungers,
[*The Joint Spectral Radius: Theory and Applications*](https://perso.uclouvain.be/raphael.jungers/sites/default/files/kcfinder/files/book.pdf),
§4.4, Open Question 7, printed p. 75 of the author manuscript.
Searches combining “joint spectral radius”, “rational matrices”, “algebraic
number”, “algebraicity”, and “transcendental” located no proof or rational-input
counterexample. The latest explicit formulation located remains the book.

## Scope

Both signs are permitted. A finite-product formula would imply
algebraicity for its particular input, but this question requires no such formula.
It concerns exact representation of a matrix computation's output, separately
from the geometry of the set of all stable inputs.

## Audit — 2026-09-10

Rechecked the indexed text of [Jungers, Open Question 7](https://perso.uclouvain.be/raphael.jungers/sites/default/files/kcfinder/files/book.pdf) and searched rational-input algebraicity and transcendence. No proof or rational counterexample was located. Failure of semialgebraic dependence on input data does not imply a transcendental value for a rational input; recent explicit open-status evidence remains unavailable.
