# TR-27 — Border-rank deficiency forcing strict submultiplicativity at the tensor square

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** Forcing a saving at exactly two copies for every projective variety goes beyond the known eventual-power mechanism and presents a general structural barrier. The relationship between degeneration and repeated decomposition matters to the tensor-complexity community.

<!-- colbrook-tensor-metrics-rank -->
**Negative resolution recorded 2026-09-11.** Matthew J. Colbrook's [complete manuscript, Theorem 1 and Section 4](../../references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr27_solution.pdf) ([LaTeX source](../../references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr27_solution.tex)) constructs a smooth, irreducible, reduced, nondegenerate complex projective curve $`X\subset\mathbb P^{11}`$ and a point $`p`$ with $`\underline R_X(p)=2`$, $`R_X(p)=3`$, and $`R_{X\times X}(p\otimes p)=9`$. This refutes the exact universal implication below, using the specified Segre product with unrestricted complex coefficients. More generally, the construction delays strict submultiplicativity for any prescribed finite number of powers; the variety depends on that prescribed delay. It does not refute versions restricted to Segre or Veronese varieties or the known eventual-power saving. The full original source passed an [independent mathematical agent review](../../references/colbrook-tensor-metrics-rank-2026-09-11/verification/reviews/TR-27-review.md). [Submission and verification record](../../references/colbrook-tensor-metrics-rank-2026-09-11/README.md). This is documented AI-assisted verification, not external human peer review; no priority claim is made. The original target and former difficulty and importance ratings are retained below as historical context.
<!-- /colbrook-tensor-metrics-rank -->

## Problem statement

Let $`V`$ be a finite-dimensional complex vector space and let $`X\subset\mathbb P(V)`$ be an irreducible reduced nondegenerate complex projective variety. Nondegenerate means that $`X`$ spans $`\mathbb P(V)`$. For $`p\in\mathbb P(V)`$, define $`R_X(p)`$ as the least number of points of $`X`$ whose projective linear span contains $`p`$. Define $`\underline R_X(p)`$ as the least $`s`$ for which $`p`$ lies in the Zariski closure of $`\{q:R_X(q)\leq s\}`$.

Embed $`X\times X`$ in $`\mathbb P(V\otimes V)`$ by the Segre map $`([x],[y])\mapsto[x\otimes y]`$. Is it always true that

```math
\underline R_X(p)<R_X(p)
\quad\Longrightarrow\quad
R_{X\times X}(p\otimes p)<R_X(p)^2?
```

Here $`p\otimes p`$ denotes the projective point represented by the tensor square of any representative of $`p`$. The product variety is precisely the Segre image just defined. For tensor-rank examples, this is the ordinary tensor product with both sets of modes retained; it does not silently merge corresponding modes into a Kronecker product.

## Why it matters

An exact tensor decomposition can require more terms than arbitrarily close decompositions. The conjecture asks whether that deficiency already yields a strict saving when two copies are decomposed together. It connects ill-behaved rank limits with the cost of repeated multilinear computation.

## References and status check

1. E. Ballico, A. Bernardi, F. Gesmundo, A. Oneto, and E. Ventura, *Geometric conditions for strict submultiplicativity of rank and border rank*, [arXiv:1909.03811v2](https://arxiv.org/html/1909.03811v2), Conjecture 1.1; Annali di Matematica Pura ed Applicata **200** (2021), 187–210.
2. A. Oneto and E. Ventura, *Ranks of tensors: geometry and applications*, [Bollettino dell'Unione Matematica Italiana **18** (2025), 751–778](https://doi.org/10.1007/s40574-025-00472-9), Conjecture 4.9.

### Status check — 2026-09-10

Checked the original v2, Conjecture 1.1 and Theorem 4.1, the 2025 restatement, and targeted strict-submultiplicativity searches through 2026. Theorem 4.1 proves the implication for all binary forms, a substantive subclass of the displayed target. The source also treats ternary cubics in Proposition 4.2 and its proof. A saving at some sufficiently large tensor power does not establish the required saving at the square. No general proof or counterexample was located; the product here retains both sets of factors.
