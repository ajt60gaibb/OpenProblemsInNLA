# RE-05 — Pure relative error for approximation by a linear matrix family

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because arbitrary matrix subspaces need pure relative error with few queries; community impact spans structured least squares and matrix compression.  
**Status:** Partially resolved  
**Area:** matrix sketching and structured least squares  
**Last checked:** 2026-09-10  

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
