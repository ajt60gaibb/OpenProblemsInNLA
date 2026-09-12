# MI-28 — Ghabries's determinant comparison for arbitrary nonnegative base powers

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale (historical):** The intermediate base powers resist the available determinantal comparisons, making the problem challenging; the immediate application is to specialist matrix-function inequalities.

## Resolution — 2026-09-11

**Solved (affirmative).** George Stepaniants's [complete proof](solution.md), **Theorem 1 and Corollary 6**, proves the displayed determinant inequality for every dimension, every complex positive definite pair, all $`k\ge0`$ and all $`0\le p\le2`$. It proves the stronger log-majorization of the corresponding normalized matrices. The proof credits Ghabries–Abbas–Mourad–Assi's published result for $`k\ge2`$ and establishes the remaining range using Furuta inequalities and a parameter interchange. [Proof PDF](solution.pdf) · [Standalone TeX](solution.tex).

The full analytic argument passed a [separate Codex-agent review](../../references/stepaniants-mi28-2026-09-11/verification/reviews/MI-28-review.md), including every exponent restriction, the noncommuting factor order, exterior powers, endpoints and exact source substitutions. It was developed with ChatGPT/Codex; the verification is independent agent review, not external human peer review or formal certification. [Authorship, source checks, reproduction and public-branch audit](../../references/stepaniants-mi28-2026-09-11/README.md). The original ID, path, target, historical ratings and earlier status check below are retained.

## Problem statement

For every integer $`n\ge1`$, positive definite matrices $`A,B\in\mathbb C^{n\times n}`$, and real parameters $`k\ge0`$, $`0\le p\le2`$, determine whether

```math
\det(A^k+|AB|^p)\ge\det(A^k+A^pB^p)
```

holds. Here $`|AB|=((AB)^*(AB))^{1/2}`$, and powers are defined by spectral functional calculus; the zeroth power of a positive definite matrix is the identity. Although the matrix inside the determinant on the right need not be Hermitian, its determinant is a positive real number: factor out $`A^k`$ and use that a product of two positive definite matrices has positive eigenvalues.

The source states the conjecture for positive semidefinite inputs. The positive definite formulation captures the nontrivial question and avoids ambiguity in zeroth powers; positive-exponent semidefinite cases follow by regularization.

Such determinants arise in comparisons of interpolants for positive definite data. The distinction between a product's modulus and the product of matrix powers is important in matrix-function inequalities.

## References

1. M. M. Ghabries, *Contributions to Matrix Inequalities and Some Applications*, PhD thesis, University of Angers and Lebanese University (2022), §2.5 and final Open Problems, Problem 1, pp. 109–110. [Thesis uploaded by its author](https://www.researchgate.net/publication/361793582_Contributions_to_Matrix_Inequalities_and_Some_Applications).
2. H. Abbas, M. M. Ghabries and B. Mourad, *New determinantal inequalities concerning Hermitian and positive semi-definite matrices*, Operators and Matrices 15 (2021), 105–116, §4, Conjecture 2, p. 116 (earlier, narrower parameter region). [Publisher PDF](https://files.ele-math.com/articles/oam-15-07.pdf).
3. M. M. Ghabries et al., *A proof of a conjectured determinantal inequality*, Linear Algebra Appl. 605 (2020), 21–28, main theorem. [Publisher](https://doi.org/10.1016/j.laa.2020.07.013).

Status check (2026-09-10): the thesis retains the range $`0< k<2`$, $`0< p<2`$, after recording proved results for $`k\ge2`$ and for $`p=2`$. Its broader question supersedes the 2021 formulation. The 2020 resolution concerns Lin's earlier $`k=2`$ question. The author's July 2026 normal-matrix determinant paper and searches for “Ghabries determinant arbitrary k conjecture”, exact titles, and 2025/2026 yielded no full resolution. This is a bounded check.
