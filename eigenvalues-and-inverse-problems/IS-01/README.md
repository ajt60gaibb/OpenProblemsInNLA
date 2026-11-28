# IS-01 — Two permutation matrices generate the doubly stochastic spectral boundary

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-11-27  

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

## Orders covered by the November 2026 preprint

Verbeken and Ginis's revised preprint proves results that imply the boundary
conjecture for $`1\le n\le 6`$ and $`n\ge 450`$. The remaining orders are
$`7\le n\le 449`$. [*Eigenvalues of doubly stochastic matrices in large orders*, arXiv:2611.30905v2](https://arxiv.org/html/2611.30905v2).

Write $`\Pi_k`$ for the convex hull of the $`k`$th roots of unity and
$`U_n=\bigcup_{k=1}^n\Pi_k`$. The preprint recalls $`D_n=U_n`$ for
$`n\le 4`$ in §1 and proves this equality for $`n=6`$ and $`n\ge 450`$.
If $`z\in\partial U_n`$, closedness places $`z`$ in one of the constituent
polygons, and $`z`$ cannot be in that polygon's interior. Thus it is a
vertex or lies on a segment joining two roots of unity of some order
$`k\le n`$. Two powers of a $`k`$-cycle, extended by $`n-k`$ fixed points,
have those two roots as eigenvalues on the same Fourier eigenvector.
Their convex combinations therefore realize the segment. This also covers
the point and segment for $`k=1,2`$.

Appendix B describes the boundary at order five. Besides the polygonal
parts, it consists of a quartic arc and its conjugate. The matrix family
$`A(t)`$ in §B.1 attains the arc and is $`tP+(1-t)Q`$. With permutations
specified by the column of the one in each row, the lists for $`P`$ and
$`Q`$ are $`(2,3,1,5,4)`$ and $`(2,3,4,1,5)`$, respectively. The same
real matrices attain the conjugate arc. [Order-five supplement, Corollary 1.2](https://arxiv.org/src/2611.30905v2/anc/small-orders/order5/proof.pdf).

In the radial description in Appendix B, each strict contraction of a
nonreal arc eigenvalue is an interior point. For $`0< s<1`$, the positive
matrix $`sA(t)+(1-s)ee^T/5`$ realizes the contracted eigenvalue on the
same sum-zero eigenvector. The real and imaginary parts of that
eigenvector span an invariant real plane perpendicular to $`e`$. A
small real perturbation on this plane, extended by zero on its
orthogonal complement, preserves both row and column sums and keeps
the matrix positive. Varying the two parts of the eigenvalue on this
plane gives an open neighborhood. Real eigenvalues are already covered
by $`U_5`$.

Theorem 5 proves $`D_n=U_n`$ analytically for $`n\ge 10^{30}`$.
Theorem 6 and Appendix A lower the threshold to 450 by a computer-assisted
proof. The order-five and order-six results in Appendix B also use
computer-assisted certificates.

On 2026-11-27, a Codex agent replayed the authors' verifier for Appendix A
(`python verify450.py --show-endpoints`) and both Appendix B verifiers
(`python verify_small_orders.py 5` and `python verify_small_orders.py 6`
from `small-orders/`). All three passed. The replay used Python 3.13.14,
python-flint 0.9.0, SymPy 1.14.0, NumPy 2.3.5 and mpmath 1.3.0 with
assertions enabled. The SHA-256 of the [unmodified v2 source archive](https://arxiv.org/src/2611.30905v2)
was `c24b7717ca42d4731d01e2569848b0a83c23bc8f1f90ed8bc0452eb31ea433a3`.
The replay checks the supplied certificates. The analytical reductions
are those of the preprint and its supplement.

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
