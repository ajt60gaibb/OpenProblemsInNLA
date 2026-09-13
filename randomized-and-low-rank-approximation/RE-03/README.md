# RE-03 — Optimal matvec query complexity of HODLR approximation

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because matching adaptive-query lower and upper bounds must cover depth and accuracy jointly; community impact is the cost of hierarchical matrix compression.  
**Status:** Partially resolved  
**Area:** information complexity of hierarchical matrix approximation  
**Last checked:** 2026-09-13  

## Partial resolution — 13 September 2026

Sidney Holden (Center for Computational Biology, Flatiron Institute, Simons Foundation) proves the following bounds in [Theorem 1.1 of the continuation manuscript](../../references/holden-re03-2026-09-13/submission/manuscript/re03_extended_results.pdf), for all original parameters and universal constants $`c,C>0`$:

```math
c\min\{n,kL/\varepsilon+k/\varepsilon^2\}
\le q_*(n,k,\varepsilon)
\le C\min\{n,kL^2/\varepsilon+kL/\varepsilon^2\}.
```

The upper bound is nonadaptive and returns a proper HODLR approximation with the original fixed-input success guarantee. Corollary 1.2 gives $`q_*=\Theta(n)`$ when $`\varepsilon\le\sqrt{k/n}`$. A separate [independent Codex AI-agent informal audit](../../references/holden-re03-2026-09-13/independent-review.md) passed these partial results, including the adaptive two-sided lower bounds. [Submission, verified affiliation, sources and reproduction limits](../../references/holden-re03-2026-09-13/README.md).

**Still open:** determine the general joint rate up to universal constants. The uncapped upper expression is $`L`$ times the lower expression, so these results do not solve the full original target. The problem remains in the open count. The available five-case assembly smoke suite passed; the historical continuation verification suite is incomplete in the supplied archive. No Lean verification, external human peer review or historical novelty claim is asserted.

## Context and notation

Use exact real arithmetic, with comparisons, standard Gaussian sampling, and exact SVDs available as primitives; charge an SVD of an $`a\times b`$ matrix $`O(ab\min(a,b))`$ operations. This states the idealized arithmetic model used here, rather than a finite precision or bit complexity claim. A matrix–vector query returns either $`Av`$ or $`A^\mathsf Tv`$ for one chosen real vector $`v`$; both types count toward the total. Randomized guarantees are for every fixed input, with probability or expectation over the algorithm's randomness.

## Problem statement

Let $`n=2^Lk`$ with integers $`k\ge1,L\ge2`$, and $`0<\varepsilon<1/2`$. Define $`\mathcal H_{n,k}`$ recursively: a matrix of order at most $`k`$ is unrestricted; at a larger node, the two equally sized diagonal blocks must satisfy the same definition, and each off-diagonal block must have rank at most $`k`$.

Let $`q_*(n,k,\varepsilon)`$ be the smallest worst-case number of queries with which a randomized adaptive algorithm, given only oracle access to an arbitrary $`A\in\mathbb R^{n\times n}`$, returns $`B\in\mathcal H_{n,k}`$ such that

```math
\Pr\!\left[
\|A-B\|_F\le(1+\varepsilon)
\min_{H\in\mathcal H_{n,k}}\|A-H\|_F
\right]\ge0.99
```

for every $`A`$. Here only oracle calls are charged: arbitrary measurable computations between queries are allowed. This is an information complexity question.

### Question

Determine $`q_*(n,k,\varepsilon)`$ up to universal multiplicative constants, including its joint dependence on $`k,L,\varepsilon`$.

## Reference

Tyler Chen, Feyza Duman Keles, Diana Halikias, Cameron Musco, Christopher Musco, and David Persson, [*Near-optimal hierarchical matrix approximation from matrix-vector products*](https://arxiv.org/pdf/2407.04686v2), SODA 2025, 2656–2692, Definition 1.1, Problem 1.1, Theorems 1.1–1.2, end of §6, and §8.

The known upper bound is $`O(\min\{n,kL^4/\varepsilon^3\})`$. The source proves $`\Omega(kL+k/\varepsilon)`$ in its regime $`n\ge c_0k/\varepsilon`$ for a sufficiently large absolute $`c_0`$; this restriction matters near the full-recovery threshold.

## Status evidence

The latest arXiv version is v2, October 24, 2024. Searches for “HODLR query complexity 2026” and “HODLR approximation 2026 lower bound” found no matching improvement. Musco's [February 2026 ICERM slides](https://app.icerm.brown.edu/assets/568/10574/10574_5858_Musco_020420261630_Slides.pdf), numbered slide 14, retain the stated upper bound. No later explicit open-status confirmation was located.

## Audit — 2026-09-10

Rechecked [Chen et al., Theorems 1.1–1.2 and §8](https://arxiv.org/html/2407.04686v2). The gap in logarithmic and accuracy factors remains. HODLR query-complexity and later hierarchical-approximation searches found no matching characterization, including the near-full-recovery regime.
