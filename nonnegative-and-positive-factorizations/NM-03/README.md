# NM-03 — Complexity of globally optimal nonnegative rank-two approximation

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Topic:** low-rank approximation; computational complexity  
**Last checked:** 2026-09-08  
**Status:** open; admitted after a bounded literature search found no resolution.  

## Problem statement

Given an arbitrary $X\in\mathbb Q_+^{m\times n}$ and
$\tau\in\mathbb Q_{\geq0}$, determine the complexity of deciding whether

$$
\exists W\in\mathbb R_+^{m\times2},\ H\in\mathbb R_+^{2\times n}:
\quad\sum_{i=1}^m\sum_{j=1}^n
\left(X_{ij}-\sum_{k=1}^2W_{ik}H_{kj}\right)^2\leq\tau.
$$

In particular, is there a deterministic algorithm polynomial in the total
binary input length, or is this decision problem NP-hard under polynomial-time
many-one reductions? This is a complexity-classification question, without
an assumption that these two outcomes exhaust the possibilities. The
factors may have real entries; only the data and threshold must be rational.
Their inner dimension is at most two, with a zero factor column permitted.

This fixes an exact decision interpretation of the literature's global
rank-two NMF optimization question. There is no promise that $X$ itself
has rank two. When a rank-two truncated SVD of $X$ is nonnegative, a best
nonnegative rank-two approximation is obtainable from it. Arbitrary input
can fall outside this tractable special case, and alternating nonnegative
least squares need not find a global optimum.

## References

Gillis, [*Nonnegative Matrix Factorization*](https://doi.org/10.1137/1.9781611976410.ch6),
§6.1.3, p. 199, Theorem 6.6 and final paragraph. Lindy, Noferini, and
Van Dooren, [*On rank-2 Nonnegative Matrix Factorizations and their variants*](https://arxiv.org/abs/2507.20612v1),
§1, with §3's suboptimal approximation and §4's ANLS initialization.

## Status check

Searches for `rank two nonnegative matrix factorization
approximation NP hard polynomial time 2025 2026` and `rank-2 NMF complexity
2026` found no resolution. The July 2025 primary paper explicitly identifies
rank two as an unresolved complexity case; its contribution is an effective
initial approximation and heuristic refinement. The March 2026
[constrained nonnegative Gram-feasibility preprint](https://arxiv.org/abs/2603.19976)
concerns partially specified symmetric matrices with affine side constraints,
which are absent from the problem above.
