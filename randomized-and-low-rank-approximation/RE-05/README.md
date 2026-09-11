# RE-05 — Pure relative error for approximation by a linear matrix family

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because arbitrary matrix subspaces need pure relative error with few queries; community impact spans structured least squares and matrix compression.  
**Status:** Solved  

<!-- colbrook-transfer -->
## Resolution — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the exact target.**

The nonadaptive two-sided algorithm achieves pure relative Frobenius error with $O(\sqrt{q(\log q+1/\varepsilon)}+\log q)$ queries at constant success. Fifteen independent copies with internal squared parameter $\varepsilon/9$ and the proved median selector give failure at most $e^{-4.8}<0.01$ and norm factor at most $1+\varepsilon$. This meets the exact canonical uniform query bound and arithmetic model.

The complete target is resolved. Its former difficulty rating is historical; the original mathematical statement and source evidence are retained below.

The manuscript acknowledges the same algorithm in an earlier public manuscript repository. The independent review now compares its available main source and supplement. No priority for the algorithm or resolution, or novelty of the logarithmic refinement, is claimed.

**Primary reference:** [complete authored PDF](../../references/colbrook-transfer-2026-09-11/manuscripts/05_linear_family_relative_sketch.pdf), [standalone TeX](../../references/colbrook-transfer-2026-09-11/manuscripts/05_linear_family_relative_sketch.tex), **Theorem 2.1 and Proposition 5.1**. [Independent proof review](../../references/colbrook-transfer-2026-09-11/verification/reviews/RE-05-review.md) · [Authorship and submission record](../../references/colbrook-transfer-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-transfer -->
**Area:** matrix sketching and structured least squares  
**Last checked:** 2026-09-11  

## Context and notation

Use exact real arithmetic, with comparisons, standard Gaussian sampling, and exact SVDs available as primitives; charge an SVD of an $a\times b$ matrix $O(ab\min(a,b))$ operations. This states the idealized arithmetic model used here, rather than a finite precision or bit complexity claim. A matrix–vector query returns either $Av$ or $A^\mathsf Tv$ for one chosen real vector $v$; both types count toward the total. Randomized guarantees are for every fixed input, with probability or expectation over the algorithm's randomness.

## Problem statement

Let $1\le q\le n^2$ and suppose linearly independent matrices $P_1,\ldots,P_q\in\mathbb R^{n\times n}$ are given explicitly. Write

$$
\mathcal L=\operatorname{span}_{\mathbb R}\{P_1,\ldots,P_q\}.
$$

An arbitrary $A\in\mathbb R^{n\times n}$ is accessible only through matrix–vector queries.

### Question

Do absolute constants $C>0$, integers $a,b\ge0$, and a uniform randomized algorithm exist that, for every $0<\varepsilon<1/2$, use at most

$$
C\sqrt q\,\varepsilon^{-a}
\bigl[1+\log(2+q)+\log(1/\varepsilon)\bigr]^b
$$

queries and return coefficients $c_1,\ldots,c_q\in\mathbb R$ such that, with probability at least $0.99$,

$$
\left\|A-\sum_{j=1}^q c_jP_j\right\|_F
\le(1+\varepsilon)\min_{D\in\mathcal L}\|A-D\|_F?
$$

Adaptive queries and unrestricted computation between queries are permitted. The displayed bound must hold uniformly over the basis and the target.

## Reference

Noah Amsel, Pratyush Avi, Tyler Chen, Feyza Duman Keles, Chinmay Hegde, Christopher Musco, Cameron Musco, and David Persson, [*Query Efficient Structured Matrix Learning*](https://arxiv.org/html/2507.19290v2), COLT 2026, PMLR **336**, 158–194, §5, linear-family conjecture; Corollary 1 has an additional term $\alpha\|A\|_F$ and query dependence on $\alpha$.

## Status evidence

The August 21, 2026 revision explicitly retains this question. Searches for “linear matrix families pure relative error” and “linearly parameterized matrix relative error 2026” found no resolution. Its abstract update resolves a related finite-family problem; finite-family discretization still produces additive error and does not automatically supply the displayed guarantee. See the [finite-family exclusion](../../references/SCREENED-OUT.md#excluded-and-uncounted-leads).

## Audit — 2026-09-10

Rechecked [Amsel et al., Corollary 1 and §5](https://arxiv.org/html/2507.19290v2). The general linear-family conjecture survives the finite-family update. [Fixed-sparsity approximation](https://doi.org/10.1137/25M1742710) uses $O(s/\varepsilon)$ queries for fixed patterns with at most $s$ entries per row. For patterns with exactly $s$ entries in every row, $q=ns$ and $s\le\sqrt q$, establishing the requested scale for this subclass; arbitrary bases remain open. Linear-family and nonadaptive follow-up searches found no general resolution.
