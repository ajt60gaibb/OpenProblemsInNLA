# PF-03 — Rational factors for rational completely positive boundary matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Historical ratings for the original target. Extreme because rational certificates on arbitrary boundary faces require new arithmetic control beyond interior geometry; community importance is exact certification in completely positive optimization.  
**Status:** Lean verified  
**Area:** exact certificates for nonnegative symmetric factorization  
**Last checked:** 2026-09-19  

## Resolution: negative, 13 September 2026

Sidney Holden (Center for Computational Biology, Flatiron Institute, Simons Foundation) gives a counterexample in [Theorem 1.1, proved in Sections 2-6](../../references/holden-pf03-2026-09-13/proof/PF03_counterexample.pdf). The exact integer matrix has order 444, rank and real cp-rank seven, and strictly positive entries. It lies on the completely positive boundary and has **no rational nonnegative factor of any finite width**. Thus it refutes the universal statement below; no classification of each smaller order or claim of minimality is needed.

The matrix is defined by the supplied signed integer matrix $`R`$ as $`A=RR^{\mathsf T}`$. An algebraic orthogonal matrix $`O`$ gives the nonnegative real factor $`RO`$. Lemma 2.1 excludes all rational nonnegative factors using a trace-zero quadratic form whose only nonzero zeros in the certified rational cone lie on seven irrational rays. Singularity is allowed by the original target and establishes boundary membership.

A separate [independent informal Codex AI-agent audit](../../references/holden-pf03-2026-09-13/independent-review.md) passed the full mathematical argument, exact facet enumeration and matrix checks. That informal audit supported **Solved** under the repository policy and did not claim Lean verification or external human peer review. The separate formal verification is recorded below. [Author, verified affiliation, exact certificates and reproduction record](../../references/holden-pf03-2026-09-13/README.md) · [Proof source](../../references/holden-pf03-2026-09-13/proof/PF03_counterexample.tex).

## Lean proof and verification evidence

**Lean verified — 19 September 2026 (UTC). Formalization: George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, with Codex assistance. Sidney Holden retains the original mathematical and exact seed-data authorship.

The [immutable Lean proof](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/9625a76780183040186664100e24e0e90d8fcc7d/nonnegative-and-positive-factorizations/PF-03/lean) proves the full original universal assertion false: some rational symmetric completely positive boundary matrix of order at least five has no rational nonnegative factor of **any positive finite width**. Boundary is taken in the space of real symmetric matrices. A proved rational halfspace representation and five zero rows replace the explicit facet enumeration. This formal witness need not have order 444, strictly positive entries, or certified minimal cp-rank; those additional source claims are outside the formalization's scope.

All 25 frozen contracts passed the local serial Lean check and two separate published-source Linux checks: the [fork run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35424055075) and [upstream PR run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35424087832). The real Comparator, default kernel, sandbox and rejection controls passed with only the three standard foundational axioms. Kernel-mode LeanCert supplies the fixed endpoint certificates used by the final proof. Two independent nonauthor AI-agent proof reviews and a separate operational evidence review passed; no official Tau Ceti service or external human peer review is claimed.

[Formalization, reproduction and scope](lean/README.md) · [Exact execution evidence](lean/verification/linux-2026-09-19/SUMMARY.json) · [Formalization metadata](lean/formalization.yaml) · [Upstream PR](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/303).

## Context and notation

A symmetric matrix $`A`$ is **completely positive** if $`A=BB^\mathsf T`$ for an entrywise nonnegative real matrix $`B`$ with finitely many columns. Let $`\mathcal{CP}_n`$ be the cone of these matrices of order $`n`$. Its **cp-rank**, $`\mathop{\mathrm{cpr}}\nolimits(A)`$, is the minimum number of columns in such a factor, with $`\mathop{\mathrm{cpr}}\nolimits(0)=0`$. Boundaries and interiors use the usual Euclidean topology on the vector space of real symmetric matrices.

## Problem statement

For every integer $`n\ge5`$ and every

```math
A\in\mathbb Q^{n\times n}\cap\partial\mathcal{CP}_n,
```

does there exist a finite integer $`m\ge1`$ and a matrix $`B\in\mathbb Q_{\ge0}^{n\times m}`$ such that

```math
A=BB^\mathsf T?
```

The width $`m`$ is unrestricted. In particular, it need not equal the real cp-rank or the order of $`A`$. This is an existence question for an exact rational certificate of complete positivity.

Rational matrices in the interior of $`\mathcal{CP}_n`$ have rational completely positive factors. Several boundary classes are also known, including matrices of rank at most two. The question concerns the remaining boundary matrices.

## References

Abraham Berman and Naomi Shaked-Monderer, [*Completely Positive Matrices over Sets*](https://cot.mathres.org/issues/COT202523.pdf), Communications in Optimization Theory (2025), article 23, §2, Question 2.1 and the explicit boundary Open Problem, p. 2. Mathieu Dutour Sikirić, Achill Schürmann, and Frank Vallentin, [*Rational factorizations of completely positive matrices*](https://doi.org/10.1016/j.laa.2017.02.017), Linear Algebra and its Applications **523** (2017), 46–51, Theorem 1.1. Max Pfeffer and José Alejandro Samper, [*The Cone of $`5\times5`$ Completely Positive Matrices*](https://link.springer.com/article/10.1007/s00454-023-00620-y), Discrete & Computational Geometry **71** (2024), 442–466, §6, Problem 6.3, discusses the order-five boundary.

## Historical status check — 2026-09-10

Rechecked [Berman–Shaked-Monderer, §2](https://cot.mathres.org/issues/COT202523.pdf) and [Oertel–Schürmann v2, §6.1.1](https://arxiv.org/html/2602.05841v2), and searched for a 2026 boundary resolution. Rank-at-most-two and other specified boundary classes have rational factors, but the 2025 paper still poses the general boundary problem. The 2026 interior theorem does not resolve it. No full boundary construction or counterexample was located; unrestricted factor width is essential.

