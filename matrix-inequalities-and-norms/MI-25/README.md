# MI-25 — Dimension-independent Hlawka constants for Schatten norms

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** Sharp cancellation constants for entire Schatten classes require new control across the Schatten scale, a challenging norm-geometry question; dimension-independent control would inform perturbation estimates across the community.

## Partial result — 2026-09-11

**Partial result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS for the stated partial result.**

The trace-norm endpoint has $`C_1=\infty`$: a real $`2\times3`$ rank-one family has defect ratio asymptotic to $`2/(3t)`$ as $`t\downarrow0`$. Zero-row padding gives the same failure on real $`3\times3`$ matrices.

**Still open:** The remaining finite Schatten exponents $`1<p<\infty`$ are undetermined by this result; the known value $`C_2=1`$ is unchanged. The ratings apply to this surviving question.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-25-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For each $`1\le p<\infty`$, determine the smallest $`C_p\in[0,\infty]`$ such that for every pair of positive integers $`N,M`$ and every $`X,Y,Z\in\mathbb C^{N\times M}`$,

```math
\|X\|_p+\|Y\|_p+\|Z\|_p-\|X+Y+Z\|_p
\le C_p\bigl(D_p(X,Y)+D_p(X,Z)+D_p(Y,Z)\bigr),
```

where $`D_p(U,V)=\|U\|_p+\|V\|_p-\|U+V\|_p`$ and $`\|U\|_p=(\sum_j s_j(U)^p)^{1/p}`$. The value $`C_p=\infty`$ means that no finite constant works uniformly over dimensions. The inequality must also hold when the parenthesized expression vanishes; a ratio definition must not discard such triples.

This asks whether the cancellation loss in a three-term matrix sum can be controlled sharply by the cancellation losses of its pairs. Such estimates concern the geometry of the matrix norms used in perturbation bounds and low-rank approximation.

## References

1. K. M. R. Audenaert and F. Kittaneh, *Problems and Conjectures in Matrix and Operator Inequalities*, arXiv:1201.5232v3 (2012), §8.2, Problem 7, equation (48), and the following discussion. [Full text](https://arxiv.org/html/1201.5232).
2. Audenaert and Kittaneh, published version in *Études opératorielles*, Banach Center Publications 112 (2017), §8.2, Problem 6, equation (48), p. 25. [Publisher PDF](https://www.impan.pl/shop/en/publication/transaction/download/product/111309).

Status check (2026-09-10): the source gives $`C_2=1`$ and demonstrates nonexistence of a finite constant for the operator norm, while posing the Schatten constants generally. Current source records and searches for “Hlawka Schatten constant”, “Hlawka operators Audenaert Kittaneh”, and 2025/2026 found no determination of all $`C_p`$. Later determinantal Hlawka inequalities concern a different inequality and do not answer this norm-deficit question. The search is bounded; individual $`p`$-cases should be rechecked before treating them as new results.
