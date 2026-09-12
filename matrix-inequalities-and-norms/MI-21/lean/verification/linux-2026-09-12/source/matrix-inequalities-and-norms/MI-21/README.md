# MI-21 — Freewan–Hayajneh inequality for sums of weighted geometric means

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** The coupled power and weight parameters make extension beyond the proved cases challenging; positive definite aggregation and matrix-function estimates give community relevance.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

Two rational positive definite $`2\times2`$ summands with $`s=t=1/2`$, $`r=2`$ and aggregate matrices $`A=B=I`$ violate the operator-norm inequality for every $`p>0`$. The left side has eigenvalue $`1351000/1350907>1`$, while the right side is one.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-21-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For positive definite matrices, define

```math
A\#_tB=A^{1/2}(A^{-1/2}BA^{-1/2})^tA^{1/2}.
```

Is the following true for all positive integers $`m,n`$, all $`A_i,B_i\in\mathbb C^{n\times n}`$ positive definite, all $`t\in[0,1]`$, and all real $`s,r,p>0`$ with $`sr\ge1`$? Set $`A=\sum_iA_i`$, $`B=\sum_iB_i`$. For every unitarily invariant norm on $`n\times n`$ matrices, does

```math
\left\|\sum_{i=1}^m(A_i^s\#_tB_i^s)^r\right\|
\le
\left\|\left(A^{(1-t)srp/2}B^{tsrp}A^{(1-t)srp/2}\right)^{1/p}\right\|
```

hold? Here all real powers of positive definite matrices use spectral functional calculus, and unitary invariance means $`\|UXV\|=\|X\|`$ for unitary $`U,V`$.

The conjecture controls the norm of a sum of nonlinear positive definite matrix means using only sums of the input matrices. It is relevant to aggregation and interpolation of positive definite data and to estimates for algorithms involving matrix powers. The full weighted statement is one problem; its individual parameter cases are not separate entries.

## References

1. S. Freewan and M. Hayajneh, *On a conjecture related to the geometric mean and norm inequalities*, Math. Inequal. Appl. 27 (2024), Conjecture 3, p. 195. [Publisher PDF](https://files.ele-math.com/articles/mia-27-15.pdf).
2. S. Freewan and M. Hayajneh, *Norm inequalities involving geometric means*, arXiv:2401.00337v1, Conjecture 1.4 and the main theorem. [Preprint](https://arxiv.org/abs/2401.00337).

Status check (2026-09-10): the current arXiv record lists v1, December 30, 2023. Its theorem treats $`t=1/2`$, $`s\ge2`$, $`r\ge1`$, $`p>0`$, $`rp\ge1`$; the abstract explicitly identifies this as a partial answer to the weighted conjecture. The original publisher text and the later preprint statement were compared. Searches for both exact titles, the authors and “weighted geometric mean conjecture”, including 2025/2026, found no full proof or counterexample. Openness is subject to this search limit.
