# IS-01 — Two permutation matrices generate the doubly stochastic spectral boundary

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Challenging reflects a global spectral-boundary description using a restricted combinatorial family; community impact connects stochastic matrices, inverse spectra, and convex geometry.

## Problem statement

Let $`\mathcal D_n`$ consist of the real entrywise-nonnegative $`n\times n`$
matrices whose row and column sums are all one, and define the single-eigenvalue
region

```math
D_n=\{z\in\mathbb C:z\in\sigma(A)\text{ for some }A\in\mathcal D_n\}.
```

Prove or disprove that, for every integer $`n\geq1`$ and every
$`z\in\partial D_n`$, there exist $`n\times n`$ permutation matrices $`P,Q`$
and $`t\in[0,1]`$ such that

```math
\det\bigl(zI-tP-(1-t)Q\bigr)=0.
```

The boundary is taken in the usual topology of $`\mathbb C`$, and $`P=Q`$
is allowed. The task concerns one eigenvalue, not simultaneous realization of
a prescribed full spectrum. It would reduce boundary computation to a finite
collection of one-parameter matrix families. Counterexamples for convex hulls
of other matrix groups do not automatically apply to all permutation matrices.

## References

Harlev, Johnson, and Lim, [*The Doubly Stochastic Single
Eigenvalue Problem: A Computational Approach*](https://arxiv.org/html/1908.03647v2),
Conjecture 2.7 and §6; published in *Experimental Mathematics* 31 (2022),
936–945. Verbeken and Ginis, [ILAS 2026 abstract](https://ilas2026.math.vt.edu/docs/ILAS2026-Book-Of-Abstracts.pdf),
p. 150.

## Earlier status check — 2026-09-08

Searches for `Harlev Johnson Lim boundary conjecture` and
`doubly stochastic boundary conjecture 2026` found the 2026 authors reporting
numerical support through order 25, rather than a proof. The older
Perfect–Mirsky conjecture fails at order five; that failure does not refute
this different assertion.

## Audit update — 2026-09-10

Rechecked the [Boundary Conjecture source](https://arxiv.org/abs/1908.03647) and the [ILAS 2026 abstracts](https://ilas2026.math.vt.edu/docs/ILAS2026-Book-Of-Abstracts.pdf), p. 150. The latter reports further computational exploration, not a general proof. Searches for subsequent doubly stochastic spectral-boundary results found no resolution; the refuted Perfect–Mirsky conjecture is a different claim.
