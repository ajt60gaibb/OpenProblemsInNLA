# MF-15 — Critical exponent for generalized doubly nonnegative matrices

**Topic:** Positivity of conventional matrix powers.  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because nonsymmetric spectral powers require a sharp dimension-uniform positivity threshold; community impact concerns matrix functions and positive matrix dynamics.  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

## Problem statement

For $n\ge3$, let $\mathcal G_n$ consist of the matrices $A\in\mathbb R^{n\times n}$ that are entrywise nonnegative, diagonalizable, and have only nonnegative real eigenvalues. Symmetry is not assumed. If

$$
A=S\operatorname{diag}(\lambda_1,\ldots,\lambda_n)S^{-1},
$$

define the conventional matrix power, for $t>0$, by

$$
A^t=S\operatorname{diag}(\lambda_1^t,\ldots,\lambda_n^t)S^{-1},
\qquad 0^t=0.
$$

Let

$$
\mathrm{CE}_n=\inf\bigl\{c\ge0:
A^t\text{ is entrywise nonnegative for every }A\in\mathcal G_n
\text{ and every real }t>c\bigr\}.
$$

Is $\mathrm{CE}_n=2(n-2)$ for every integer $n\ge3$?

## Why it matters

This asks for the exact dimension-dependent threshold beyond which spectral matrix powers preserve entrywise positivity in a nonsymmetric class, relevant to matrix functions and positive dynamics.

## References

- X. Han, C. R. Johnson, and P. Paparella, [The critical exponent for generalized doubly nonnegative matrices](https://arxiv.org/abs/1407.7059), *Linear and Multilinear Algebra* 65 (2017), 1035–1044, §1 for definitions, Theorem 3.3 for an upper bound, Corollary 4.5 for $n=3$, and Question 4.7 for the displayed formula. The conjectural $n=4$ case is Conjecture 4.6.
- D. Guillot, A. Khare, and B. Rajaratnam, [The critical exponent conjecture for powers of doubly nonnegative matrices](https://arxiv.org/abs/1303.4701), *Linear Algebra and its Applications* 439 (2013), 2422–2427, abstract and main theorem: resolution of the symmetric case.

## Status check

On 2026-09-08, checked the latest listed arXiv version and searched “generalized doubly nonnegative”, “critical exponent”, “2(n-2)”, “conjecture”, and 2025–2026. No resolution of Question 4.7 was located. The source proves existence of a finite threshold and $\mathrm{CE}_3=2$. The solved symmetric doubly nonnegative problem has threshold $n-2$ and concerns a smaller class; results for entrywise (Hadamard) powers concern a different operation. The special case $n=4$ and related integrality questions are included within this single target, not counted separately. No recent explicit reaffirmation was found.

## Audit — 2026-09-10

Rechecked [Han–Johnson–Paparella, Corollary 4.5 and Question 4.7](https://arxiv.org/pdf/1407.7059). The $n=3$ equality is proved; the all-dimensions formula remains posed. Generalized-DN critical-exponent searches found no later resolution. The [published record](https://doi.org/10.1080/03081087.2016.1223009) confirms the 2017 article; symmetric and entrywise-power theorems do not settle it.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
