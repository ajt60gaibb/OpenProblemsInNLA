# RA-17 — Minimum linear measurements for uniform recovery of real low-rank matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-13

**Rating rationale:** The all-dimension real measurement classification needs new control of exceptional kernels and topological obstructions, hence challenging. Its main impact is on the community working on low-rank matrix sensing and recovery.

## Problem statement

For integers $`d\geq2`$ and $`1\leq r\leq\lfloor d/2\rfloor`$, let

```math
\mathcal M_{d,r}(\mathbb R)=\{X\in\mathbb R^{d\times d}:\mathop{\mathrm{rank}}\nolimits X\leq r\}.
```

For real measurement matrices $`A_1,\ldots,A_m`$, define

```math
\mathcal A(X)=
(\mathop{\mathrm{tr}}\nolimits(A_1^\top X),\ldots,\mathop{\mathrm{tr}}\nolimits(A_m^\top X)).
```

Determine the exact integer

```math
\mu_{\mathbb R}(d,r)=
\min\{m:\exists A_1,\ldots,A_m\in\mathbb R^{d\times d},\
\mathcal A|_{\mathcal M_{d,r}(\mathbb R)}\text{ is injective}\}
```

for all such $`d,r`$.

Injectivity is uniform: every two matrices of rank at most $`r`$ with equal measurements must coincide. Equivalently, $`\ker\mathcal A`$ must contain no nonzero matrix of rank at most $`2r`$. No randomness, stability guarantee, computationally efficient decoder, positive semidefiniteness, or generic-signal exception is required. The problem concerns unrestricted real square matrices and unrestricted real linear measurements.

## Partial continuation — 13 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation ([verified affiliation](../../references/holden-ra17-continuation-2026-09-13/SUBMISSION.md)).

The [continuation manuscript](../../references/holden-ra17-continuation-2026-09-13/writeup/RA17_topological_relaxation.pdf), Sections 3–4, characterizes two topological relaxations one measurement below the complex generic count: existence of a continuous odd nonvanishing map on the low-rank unit link, and existence of the corresponding number of independent continuous evaluation-bundle sections. Each is equivalent to even complex determinantal degree. These do not establish a system of constant linear measurement matrices. Section 5 rederives the rank-one index lower bound; Section 2 supplies integer upper-bound measurements.

The [independent informal AI-agent review](../../references/holden-ra17-continuation-2026-09-13/independent-review.md) records the checked scope and arithmetic verification. [Source, code and provenance](../../references/holden-ra17-continuation-2026-09-13/README.md). No Lean verification or external human peer review is asserted. This extends the earlier partial submission in [PR #197](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/197); no priority claim is made.

**Remaining target:** the exact count for every allowed pair. In particular, the submission leaves $`19\leq\mu_{\mathbb R}(6,1)\leq20`$ and $`35\leq\mu_{\mathbb R}(10,1)\leq36`$ undecided. Section 7 identifies the missing existence or impossibility of a 17-dimensional real space of six-by-six matrices with every nonzero matrix of rank at least three. RA-17 remains **Partially resolved** and counted as open.

## Why it matters

This is the information-theoretic limit of noiseless real matrix sensing. It distinguishes intrinsic identifiability from the larger measurement budgets that particular algorithms or stability guarantees may require.

## References and status check

1. Z. Xu, *Signal Recovery on Algebraic Varieties Using Linear Samples*, [arXiv:2506.17572](https://arxiv.org/pdf/2506.17572), §5, Problem 5.1 and Remark 5.6, pp.13–15; published in [Acta Mathematica Sinica **42** (2026), 740–754](https://doi.org/10.1007/s10114-026-5299-y).
2. Z. Xu, *The minimal measurement number for low-rank matrix recovery*, [Applied and Computational Harmonic Analysis](https://doi.org/10.1016/j.acha.2017.01.005), the original real counterexample and complex exact-count results cited as reference 18 in the survey.

The 2026 survey explicitly retains the real problem. It gives $`\mu_{\mathbb R}(d,r)\leq4dr-4r^2`$ and equality in specified dimension families, while its real $`(d,r)=(4,1)`$ construction uses 11 measurements rather than the complex threshold 12. Thus the uniformly asserted equality with the complex count is already false and is not proposed here. The complex count itself is solved. Current version checks and searches for Xu, the exact title, and 2025–2026 minimal real low-rank measurements found no general resolution.

## Audit — 2026-09-10

Independently rechecked [Xu, Theorem 5.5 and Remark 5.6](https://arxiv.org/html/2506.17572v2), the unchanged June 2025 arXiv v2 record, and the [2026 publication](https://actamath.cjoe.ac.cn/Jwk_sxxb_en/EN/10.1007/s10114-026-5299-y). Equality is proved when $`d=2^k+r`$ (subject to the stated rank range) or $`d=2r+1`$, so Partially resolved is warranted. Targeted later searches found no full real measurement-count classification. Changed extreme/broad ratings to challenging/community, matching the concrete exceptional-kernel obstacle and the scope of noiseless matrix sensing. The unresolved aim is a general sharp formula or classification in $`d,r`$; individual fixed cases can already be expressed as decidable real polynomial feasibility problems.
