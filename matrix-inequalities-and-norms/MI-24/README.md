# MI-24 — Schatten norm complement involving Lin's positive definite quantity

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale (historical):** Extending the proved trace and Frobenius cases to all Schatten norms is challenging; the comparison of these particular means has specialist importance.

## Resolution — 2026-09-11

**Solved (affirmative).** George Stepaniants's [complete proof](solution.md), **Theorem 1**, proves the displayed inequality for every dimension, every complex positive definite pair and every $`1\le p\le\infty`$. The published Heron norm inequality and a positive matrix comparison give $`\|A+B+2G\|_p\le\|A+B+G+L\|_p`$. Since $`2(A+B+G+L)=(A+B+2G)+(A+B+2L)`$, the triangle inequality then proves the desired comparison. [Proof PDF](solution.pdf) · [Standalone TeX](solution.tex).

The complete argument and its precise published input passed a [separate Codex-agent review](../../references/stepaniants-mi24-2026-09-11/verification/reviews/MI-24-review.md). It was developed with ChatGPT/Codex; the verification is independent agent review, not external human peer review or formal certification. [Authorship, source checks, reproduction and public-branch audit](../../references/stepaniants-mi24-2026-09-11/README.md). The contribution is the convexity deduction from existing comparisons. The original ID, path, statement, historical ratings and earlier status check below remain intact.

## Problem statement

For positive definite $`A,B\in\mathbb C^{n\times n}`$, set

```math
G=A^{1/2}(A^{-1/2}BA^{-1/2})^{1/2}A^{1/2},\qquad
L=A^{1/2}(B^{1/2}A^{-1}B^{1/2})^{1/2}A^{1/2}.
```

Here $`G=A\#B`$, while $`L`$ is the explicitly defined quantity used by Lin; no symmetry of $`L(A,B)`$ is assumed. Determine whether, for all $`n\ge1`$, all positive definite $`A,B`$, and all $`1\le p\le\infty`$,

```math
\|A+B+G+L\|_p\le\|A+B+2L\|_p.
```

For $`p<\infty`$, $`\|X\|_p=(\mathop{\mathrm{tr}}\nolimits|X|^p)^{1/p}`$, where $`|X|=(X^*X)^{1/2}`$; for $`p=\infty`$, use the largest singular value.

Matrix means are central to interpolation of positive definite data. The conjecture supplies a norm comparison between two concrete sums of matrix functions; eigenvalue comparison between $`G`$ and $`L`$ alone is not the statement being requested.

## References

1. M. M. Ghabries, H. Abbas, B. Mourad and A. Assi, *New log-majorization results concerning eigenvalues and singular values and a complement of a norm inequality*, preprint (2021), definition in §4, p. 11; Conjecture 4.1, p. 13. [PDF](https://arxiv.org/pdf/2105.13356); [journal article](https://doi.org/10.1080/03081087.2022.2059050).
2. M. M. Ghabries, *Contributions to Matrix Inequalities and Some Applications*, PhD thesis (2022), final Open Problems, Problem 5, pp. 109–110. [Author-uploaded thesis](https://www.researchgate.net/publication/361793582_Contributions_to_Matrix_Inequalities_and_Some_Applications).

Status check (2026-09-10): the first source proves $`p=1,2`$ and then conjectures the full interval. The thesis explicitly retains that gap. Current arXiv version v1, published metadata, the author's later July 2026 matrix-mean paper, and searches for “Ghabries Conjecture 4.1 norm”, “Lin complement geometric mean Schatten”, including 2025/2026, did not reveal a proof or counterexample for the full interval. No assertion of exhaustive coverage is made.
