# MF-09 — Decidability of strict stability for rational matrix families

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because termination at an unpromised strict threshold is a foundational decidability barrier; broad impact includes switched control and algorithmic matrix-product theory.  
**Status:** Open  
**Last checked:** 2026-09-10  

## Context and notation

The joint spectral radius of a nonempty compact set $`\mathcal M\subset\mathbb C^{d\times d}`$ is

```math
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
```

This definition also applies to finite real matrix sets. The ordinary spectral
radius of one matrix is written $`\rho(A)`$.

## Problem statement

Does a Turing machine exist which, on every input consisting of a
finite nonempty list of matrices in $`\mathbb Q^{d\times d}`$, encoded by binary
integer numerators and positive denominators, halts and correctly decides whether

```math
\widehat\rho(\mathcal M)<1?
```

Dimension and list length are part of the input. No separation from the threshold
is promised. The question asks for termination and correctness, without a
polynomial running-time requirement.

## References and status evidence

Jungers,
[*The Joint Spectral Radius: Theory and Applications*](https://perso.uclouvain.be/raphael.jungers/sites/default/files/kcfinder/files/book.pdf),
§2.2.3, Open Question 1, printed p. 29 of the author manuscript. Blondel and Tsitsiklis,
[The boundedness of all products of a pair of matrices is undecidable](https://www.sciencedirect.com/science/article/abs/pii/S0167691100000499),
Systems & Control Letters 41 (2000), 135–140, §2, proves undecidability of
the non-strict test $`\widehat\rho\le1`$. That theorem does not answer the
strict test.

The screen included “joint spectral radius” with “strict”, “decidability”,
“less than one”, and 2025/2026. No deciding algorithm or applicable undecidability
reduction was located. Some later literature summarizes the non-strict theorem
as a generic stability impossibility; admission here follows its actual threshold.
[MF-04](../MF-04/README.md) is a proposed finite-product property, whereas this entry asks for a decision
procedure even if such a property fails.

## Audit — 2026-09-10

Rechecked the indexed text of [Jungers, Open Question 1](https://perso.uclouvain.be/raphael.jungers/sites/default/files/kcfinder/files/book.pdf) and strict-stability/decidability searches. No deciding algorithm or applicable undecidability theorem was located. [Daubechies–Lagarias' correction](https://websites.umich.edu/~lagarias/doc/corr-infprod.pdf) independently distinguishes the unresolved subunit test from the undecidable unit-threshold problem. Evidence remains historical and bounded.
