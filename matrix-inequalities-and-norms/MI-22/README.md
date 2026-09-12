# MI-22 — Lemos–Soares singular-value log-majorization

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** Controlling every partial product of singular values is challenging despite the proved eigenvalue-modulus analogue; the resulting norm comparisons are relevant across matrix analysis.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

Rational positive definite $`3\times3`$ matrices at $`t=1/8`$ violate the first singular-value inequality: the left operator norm exceeds 10900, while $`\|AB\|_2<10200`$. Exact rational root residuals and a proved operator-root error bound certify the actual principal powers.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-22-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

Let $`A,B\in\mathbb C^{n\times n}`$ be positive definite and $`t\in[0,1]`$, and define $`A\#_tB=A^{1/2}(A^{-1/2}BA^{-1/2})^tA^{1/2}`$. Write $`s_1(X)\ge\cdots\ge s_n(X)`$ for the singular values of $`X`$.

Does

```math
\prod_{j=1}^k s_j\bigl(A^t(A\#_tB)B^{1-t}\bigr)
\le\prod_{j=1}^k s_j(AB),\qquad 1\le k< n,
```

hold for every positive integer $`n`$, every such $`A,B,t`$, with equality of the products for $`k=n`$? This is the assertion $`s(A^t(A\#_tB)B^{1-t})\prec_{\log}s(AB)`$. The positive semidefinite version in the sources is recovered by continuous regularization $`A+\varepsilon I,B+\varepsilon I`$; endpoints in $`t`$ can be stated directly.

The question concerns the singular values of a product involving a matrix geometric mean. Such multiplicative bounds imply norm and determinant estimates useful in numerical treatment of positive definite matrices. An analogue for eigenvalue moduli has already been proved, but changes both sides of the comparison and does not answer this singular-value question.

## References

1. M. M. Ghabries, H. Abbas, B. Mourad and A. Assi, *New log-majorization results concerning eigenvalues and singular values and a complement of a norm inequality*, Linear Multilinear Algebra 71 (2023), 1228–1243; preprint Conjecture 1.1, p. 3, and §3. [Full preprint](https://arxiv.org/pdf/2105.13356); [published article](https://doi.org/10.1080/03081087.2022.2059050).
2. J. Shi, Z. Wang and C. Wei, *Log-majorizations of Lemos–Soares type for the metric geometric and spectral geometric means*, Ann. Funct. Anal. 17 (2026), article 53, p. 3, equation (1.2) and the following open-status statement. [Publisher](https://doi.org/10.1007/s43034-026-00532-x); [publicly indexed full-text mirror](https://www.scribd.com/document/1073369698/s43034-026-00532-x).

Status check (2026-09-10): the original arXiv record lists v1. The July 14, 2026 paper reproduces precisely this inequality as (1.2) on p. 3 and explicitly says that it is still open. The publisher PDF was inaccessible, but the indexed primary-paper text in the public mirror exposed this passage and the later discussion distinguishing the new partial results. Searches for “Lemos Soares singular log-majorization conjecture”, the exact later title, and 2025/2026 found no subsequent announced full resolution. This is a bounded search, not certification of openness.
