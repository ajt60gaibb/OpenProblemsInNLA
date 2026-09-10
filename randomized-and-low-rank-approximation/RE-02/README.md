# RE-02 — HSS approximation from a number of matvecs independent of depth

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because reusing sketches introduces dependencies across the hierarchy; community impact is reducing operator access in black-box HSS compression.  
**Status:** Open  
**Area:** randomized matrix compression  
**Last checked:** 2026-09-10  

## Context and notation

Use exact real arithmetic, with comparisons, standard Gaussian sampling, and exact SVDs available as primitives; charge an SVD of an $a\times b$ matrix $O(ab\min(a,b))$ operations. This states the idealized arithmetic model used here, rather than a finite precision or bit complexity claim. A matrix–vector query returns either $Av$ or $A^\mathsf Tv$ for one chosen real vector $v$; both types count toward the total. Randomized guarantees are for every fixed input, with probability or expectation over the algorithm's randomness.

For $N=2^{L+1}k$, $k,L\ge1$, form the perfect binary tree that successively halves the ordered index set $[N]=\{1,\ldots,N\}$ until every leaf contains $2k$ indices. Define $\mathcal S_{L,k}$ to contain precisely the real $N\times N$ matrices $B$ such that, for every nonroot node $I$ of this tree,

$$
\operatorname{rank}B[I,[N]\setminus I]\le k,
\qquad
\operatorname{rank}B[[N]\setminus I,I]\le k.
$$

This is the HSS class with rank at most $k$, including its constraints across levels. There is no restriction inside a leaf diagonal block. Set

$$
E_{L,k}(A)=\min_{B\in\mathcal S_{L,k}}\|A-B\|_F^2.
$$

The minimum exists. The rank definition follows Stefano Massei, Leonardo Robol, and Daniel Kressner, [*hm-toolbox: MATLAB Software for HODLR and HSS Matrices*](https://arxiv.org/pdf/1909.07909v3), SIAM Journal on Scientific Computing **42** (2020), C43–C68, §2.2, Definition 3. Equivalence with the telescoping representation and existence of a minimizer are recorded in Amsel et al., cited below, Definition 3 and Appendix D.

## Problem statement

Do absolute constants $C_q,C_e,c>0$ and a uniform randomized algorithm exist that, for every $k,L\ge1$ and every $A\in\mathbb R^{N\times N}$, $N=2^{L+1}k$, accesses $A$ solely through at most $C_qk$ matrix–vector queries and returns $B\in\mathcal S_{L,k}$ satisfying

$$
\mathbb E\|A-B\|_F^2\le C_e L\,E_{L,k}(A),
$$

with at most $O(N^c)$ additional arithmetic operations? Queries may be adaptive. The budget counts both transpose and forward products and is a bound on every execution.

## References

Amsel et al., [*Quasi-optimal Hierarchically Semi-separable Matrix Approximation*](https://arxiv.org/html/2505.16937v2), §1.2, Theorem 13, §§4.4–5. James Levitt and Per-Gunnar Martinsson, [*Linear-Complexity Black-Box Randomized Compression of Rank-Structured Matrices*](https://arxiv.org/pdf/2205.02990v3), SIAM Journal on Scientific Computing **46** (2024), A1747–A1763, Algorithm 4.1 and Remark 4.3.

## Status evidence

The proved guarantee uses $O(kL)$ queries. Reusing sketches reduces the query count, but its approximation guarantee remains unproved. Searches for “HSS O(k) approximation 2026 matvec” and “HSS approximation logarithmic 2026” found no resolution. Levitt–Martinsson's latest arXiv version is v3, submitted June 21, 2024. Christopher Musco's [February 2026 ICERM slides](https://app.icerm.brown.edu/assets/568/10574/10574_5858_Musco_020420261630_Slides.pdf), numbered slide 14, still list $O(k\log N)$ queries for HSS approximation.

[RE-01](../RE-01/README.md) permits full access and asks for a constant error factor. RE-02 retains the known dependence of the error factor on depth and asks for fewer queries. Neither target directly implies the other.

## Audit — 2026-09-10

Rechecked [Amsel et al., Theorem 13 and §4.4](https://arxiv.org/html/2505.16937v2). The proved approximation uses depth-dependent queries; the reused-sketch algorithm lacks the requested guarantee. HSS matvec and later-publication searches found no resolution with a query count independent of depth.
