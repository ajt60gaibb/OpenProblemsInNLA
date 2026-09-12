# MD-03 — The Komlós discrepancy conjecture

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Provenance:** source-stated conjecture.  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** Dimension-free vector balancing is a foundational discrepancy barrier with wide implications for rounding, optimization and algorithms.

## Resolution — 2026-09-11

**Affirmative resolution by Shengtao Guo, Ethan X. Fang and Junwei Lu**, [*Vector Balancing via Directional Total Variation*, arXiv:2609.11189v1](https://arxiv.org/abs/2609.11189v1), submitted 10 September 2026, **Theorem 1.1, p. 1**. It proves the displayed target with the universal constant $`C=3\sqrt{2\pi}`$; its strict bound is stronger than the requested non-strict inequality. Each column of $`A`$ is one of the theorem's vectors. All positive dimensions and every column are covered; no algorithmic assertion is required.

**Application note by George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology: [proof by reference](solution.md), **Theorem 1** ([PDF](../../references/stepaniants-2026-09-11/manuscripts/md03_md04_proofs.pdf) · [LaTeX](../../references/stepaniants-2026-09-11/manuscripts/md03_md04_proofs.tex)). Stepaniants authors this explanatory note; the discrepancy theorem is credited to Guo, Fang and Lu.

A separate Codex agent checked both the application and the substantive source proof, including its published eigenvalue-convexity input, and returned **PASS**: [independent review](../../references/stepaniants-2026-09-11/verification/reviews/MD-03-MD-04-review.md). This is independent automated-agent verification under the repository's status definition, not external human peer review or formal certification. The source remains a preprint and discloses Odin AI use. The application draft was prepared with ChatGPT. The original statement and dated history below are retained; the ratings above are historical. [Submission record](../../references/stepaniants-2026-09-11/README.md).

## Problem statement

Does a finite constant $`C>0`$ exist such that, for every pair of positive integers $`m,n`$ and every matrix $`A=(a_{ij})\in\mathbb R^{m\times n}`$ satisfying

```math
\sum_{i=1}^m a_{ij}^2\leq1\qquad(1\leq j\leq n),
```

there is a vector $`x\in\{-1,1\}^n`$ for which

```math
\|Ax\|_\infty=\max_{1\leq i\leq m}\left|\sum_{j=1}^n a_{ij}x_j\right|\leq C?
```

The same constant must work for every dimension and matrix. The question asks for existence of a signing; it does not additionally require an algorithm.

This is a matrix balancing problem: choose column signs so that their sum is small in every coordinate. Its norm constraint and simultaneous coordinate control connect discrepancy theory with rounding and linear optimization.

## References

1. N. Bansal and H. Jiang, *An Exposition of the $`\widetilde O(\log^{1/4}n)`$ Bound for the Komlós Problem*, arXiv:2608.28452 (2026), abstract and introduction, including the explicit conjecture and the new dimension-dependent bound. [Paper](https://arxiv.org/html/2608.28452v1).
2. N. Bansal and H. Jiang, *Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlós Bounds Beyond Banaszczyk*, arXiv:2508.03961v2 (2025), abstract and introductory results. [Paper](https://arxiv.org/abs/2508.03961).
3. W. Banaszczyk, *Balancing vectors and Gaussian measures of n-dimensional convex bodies*, Random Structures & Algorithms 12(4) (1998), pp. 351–360, the main vector-balancing theorem underlying the earlier logarithmic bound. [Article](https://onlinelibrary.wiley.com/doi/abs/10.1002/%28SICI%291098-2418%28199807%2912%3A4%3C351%3A%3AAID-RSA3%3E3.0.CO%3B2-S).

## Earlier status check — 2026-09-10

checked the current arXiv records (2608.28452v1, 2026-08-28; 2508.03961v2, 2025-09-09) and searched “Komlos conjecture solved proof September 2026” and “Komlos Bansal Jiang 2026 bound”. The new bound is $`O((\log n)^{1/4}(\log\log n)^{7/4})`$ in its asymptotic range, not a universal constant. No full proof, counterexample, or withdrawal of these source papers was found. The disproved Hajela conjecture and the separate matrix Spencer conjecture are not this statement.

**Audit update (2026-09-10):** Rechecked the August 2026 exposition and searched for later Komlós resolutions. Its improved dimension-dependent bound still leaves the universal-constant target open. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
