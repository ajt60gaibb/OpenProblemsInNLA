# MI-26 — Concave unitary-orbit subadditivity without monotonicity

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** Removing monotonicity from a unitary-orbit comparison is challenging; spectral bounds for broad classes of matrix functions have community importance.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

The real-valued concave function $`f(x)=x-x^2`$ and two rational projections refute the two-unitary inequality; an explicit positive definite variant also works. The allowed condition is $`f(0)\ge0`$, without global nonnegativity or monotonicity. This does not refute the narrower nonnegative-valued function class.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-26-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For every integer $`n\ge1`$, positive semidefinite matrices $`A,B\in\mathbb C^{n\times n}`$, and real-valued concave function $`f:[0,\infty)\to\mathbb R`$ with $`f(0)\ge0`$, must there exist unitary matrices $`U,V\in\mathbb C^{n\times n}`$ such that

```math
f(A+B)\preceq Uf(A)U^*+Vf(B)V^*?
```

Here $`X\preceq Y`$ means $`Y-X`$ is positive semidefinite, $`U^*U=UU^*=I`$, and $`f(A)`$ is defined by applying $`f`$ to the eigenvalues in a spectral decomposition of $`A`$. Concavity means

```math
f(\theta x+(1-\theta)y)\ge\theta f(x)+(1-\theta)f(y)
\quad (x,y\ge0,\ 0\le\theta\le1).
```

The function is not assumed nonnegative on its entire domain; adding that assumption would change the problem. The unitaries may depend on $`A,B,f`$.

The requested inequality is an order comparison between sums of matrix functions up to changes of orthonormal basis. Such comparisons yield spectral and norm bounds for nonlinear transformations of positive semidefinite matrices.

## References

1. K. M. R. Audenaert and F. Kittaneh, *Problems and Conjectures in Matrix and Operator Inequalities*, arXiv:1201.5232v3 (2012), §2, Problem 5 and equation (11). [Full text](https://arxiv.org/html/1201.5232).
2. J.-C. Bourin and E.-Y. Lee, *Unitary orbits of Hermitian operators with convex or concave functions*, Bull. Lond. Math. Soc. 44 (2012), 1085–1102, Theorem 3.1 and Remark 3.13. [Preprint](https://arxiv.org/html/1109.2384).

Status check (2026-09-10): the two sources explicitly leave removal of monotonicity open. The published 2017 Audenaert–Kittaneh update also retains the question. Searches for “concave unitary subadditivity monotonicity”, “Bourin Lee nonmonotone concave”, and 2025/2026, together with the new arXiv:2609.05854 paper on Horn and orbit inequalities, found no stated resolution of this full function class. Recent results for nonnegative concave functions impose a stronger assumption. This is a bounded status check.
