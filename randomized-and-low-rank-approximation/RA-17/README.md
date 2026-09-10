# RA-17 — Minimum linear measurements for uniform recovery of real low-rank matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** The all-dimension real measurement classification needs new control of exceptional kernels and topological obstructions, hence challenging. Its main impact is on the community working on low-rank matrix sensing and recovery.

## Problem statement

For integers $d\geq2$ and $1\leq r\leq\lfloor d/2\rfloor$, let
$$
\mathcal M_{d,r}(\mathbb R)=\{X\in\mathbb R^{d\times d}:\operatorname{rank}X\leq r\}.
$$
For real measurement matrices $A_1,\ldots,A_m$, define
$$
\mathcal A(X)=
(\operatorname{tr}(A_1^\top X),\ldots,\operatorname{tr}(A_m^\top X)).
$$
Determine the exact integer
$$
\mu_{\mathbb R}(d,r)=
\min\{m:\exists A_1,\ldots,A_m\in\mathbb R^{d\times d},\
\mathcal A|_{\mathcal M_{d,r}(\mathbb R)}\text{ is injective}\}
$$
for all such $d,r$.

Injectivity is uniform: every two matrices of rank at most $r$ with equal measurements must coincide. Equivalently, $\ker\mathcal A$ must contain no nonzero matrix of rank at most $2r$. No randomness, stability guarantee, computationally efficient decoder, positive semidefiniteness, or generic-signal exception is required. The problem concerns unrestricted real square matrices and unrestricted real linear measurements.

## Why it matters

This is the information-theoretic limit of noiseless real matrix sensing. It distinguishes intrinsic identifiability from the larger measurement budgets that particular algorithms or stability guarantees may require.

## References and status check

1. Z. Xu, *Signal Recovery on Algebraic Varieties Using Linear Samples*, [arXiv:2506.17572](https://arxiv.org/pdf/2506.17572), §5, Problem 5.1 and Remark 5.6, pp.13–15; published in [Acta Mathematica Sinica **42** (2026), 740–754](https://doi.org/10.1007/s10114-026-5299-y).
2. Z. Xu, *The minimal measurement number for low-rank matrix recovery*, [Applied and Computational Harmonic Analysis](https://doi.org/10.1016/j.acha.2017.01.005), the original real counterexample and complex exact-count results cited as reference 18 in the survey.

The 2026 survey explicitly retains the real problem. It gives $\mu_{\mathbb R}(d,r)\leq4dr-4r^2$ and equality in specified dimension families, while its real $(d,r)=(4,1)$ construction uses 11 measurements rather than the complex threshold 12. Thus the uniformly asserted equality with the complex count is already false and is not proposed here. The complex count itself is solved. Current version checks and searches for Xu, the exact title, and 2025–2026 minimal real low-rank measurements found no general resolution.

## Audit — 2026-09-10

Independently rechecked [Xu, Theorem 5.5 and Remark 5.6](https://arxiv.org/html/2506.17572v2), the unchanged June 2025 arXiv v2 record, and the [2026 publication](https://actamath.cjoe.ac.cn/Jwk_sxxb_en/EN/10.1007/s10114-026-5299-y). Equality is proved when $d=2^k+r$ (subject to the stated rank range) or $d=2r+1$, so Partially resolved is warranted. Targeted later searches found no full real measurement-count classification. Changed extreme/broad ratings to challenging/community, matching the concrete exceptional-kernel obstacle and the scope of noiseless matrix sensing. The unresolved aim is a general sharp formula or classification in $d,r$; individual fixed cases can already be expressed as decidable real polynomial feasibility problems.
