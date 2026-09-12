# MI-09 — Sharp Schatten triangle constants for the arithmetic symmetric modulus

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** The unresolved Schatten parameters require sharp nonnormal extremizers; their direct impact is the quantitative theory of symmetric moduli.

## Partial result — 2026-09-11

**Partial result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS for the stated partial result.**

For every $`m\ge2`$, the exact dimension-two operator-norm constant is $`c_\infty^{\rm sym}(m,2)=\sqrt{6\sqrt3-9}`$. This is also the sharp single constant valid simultaneously for every unitarily invariant norm on $`M_2`$.

**Still open:** This does not determine each individual finite Schatten constant. The cases $`1< p<\infty`$ remain open; the previously established trace endpoint and higher-dimensional operator endpoint are retained. The ratings apply to this surviving question.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-09-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For $`X\in\mathbb C^{n\times n}`$ set $`S(X)=((X^*X)^{1/2}+(XX^*)^{1/2})/2`$. Let $`\|X\|_p=(\sum_i\sigma_i(X)^p)^{1/p}`$ for $`1\le p<\infty`$, with $`\|X\|_\infty=\sigma_1(X)`$. Determine, for all integers $`m,n\ge2`$ and all $`p\in[1,\infty]`$, the exact value

```math
c_p^{\rm sym}(m,n)=\sup_{(A_1,\ldots,A_m)\ne(0,\ldots,0)}
\frac{\|S(A_1+\cdots+A_m)\|_p}{\|S(A_1)+\cdots+S(A_m)\|_p},
\qquad A_j\in\mathbb C^{n\times n}.
```

The denominator is positive on the stated domain. A resolution should identify the value for the unsolved parameters while retaining known endpoint values.

## Why it matters

This asks how much the symmetric positive representative of a matrix sum can exceed the sum of the individual representatives in Schatten norm. Sharp constants quantify the loss in this way of bounding nonnormal matrix sums.

## References

1. T. Zhang, *Operator symmetric moduli and sharp triangle inequalities*, arXiv:2603.01046v1 (1 March 2026), Problem 1.17 and §8. [Primary text](https://arxiv.org/html/2603.01046).
2. J.-C. Bourin and E.-Y. Lee, *Some hybrid matrix triangle inequalities*, arXiv:2606.29188v1 (28 June 2026), introduction and Theorem 1.3, for the dimension-independent majorization bound. [Primary text](https://arxiv.org/html/2606.29188).

## Status check — 2026-09-10

The source proves $`c_1^{\rm sym}=1`$ and $`c_\infty^{\rm sym}=\sqrt2`$ when $`n\ge3`$, and gives bounds for the other cases. Its latest version remains v1. Searches included `arithmetic symmetric modulus optimal Schatten constants`, `Zhang Problem 1.17 symmetric modulus`, and both paper titles with `2026 sharp`. No general determination was found. Problem 1.11's two-dimensional restriction is subsumed here and is not counted as an additional entry. Unlike the unitary-orbit conjecture, this problem asks for exact norm extrema, not a positive-semidefinite domination.

**Audit update (2026-09-10):** Rechecked Zhang Problem 1.17, including its endpoint values, and the June hybrid estimates. Searches for exact arithmetic-symmetric Schatten constants found no all-parameter answer; the displayed target includes the proved endpoints. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
