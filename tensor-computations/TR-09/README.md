# TR-09 — Subquadratic overparameterization for iterative decomposition of smoothed tensors

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because a uniform convergence guarantee must handle arbitrary smoothed factors, random initialization and near-exact recovery below quadratic overparameterization; broad importance includes nonconvex optimization and machine learning.  
**Status:** Open  
**Last checked:** 2026-09-13

## Supporting results — 2026-09-13

Sidney Holden (Center for Computational Biology, Flatiron Institute, Simons Foundation) gives [local ALS rates and a separate algebraic comparator](../../references/holden-tr09-2026-09-13/report.pdf). Theorem 4.1 and Corollary 4.2 prove a derivative bound and pointwise local convergence for a specified mixed-block ALS cycle when two normalized factor Gram matrices are close to identity. Theorem 5.1 supplies a smoothing event for two orthogonal base modes. Theorem 7.1 gives exact $`2r-1`$-term algebraic recovery under its stated rank and noncollinearity assumptions.

**TR-09 remains Open.** No input-independent random-start basin probability is proved, even for the restricted base family. The global algebraic method is outside the required optimization class. The supporting proofs passed a separate [independent informal Codex AI-agent review](../../references/holden-tr09-2026-09-13/independent-review.md); this does not establish a full or restricted random-start resolution. [Authorship, verified affiliation and provenance](../../references/holden-tr09-2026-09-13/README.md). No Lean verification, external human peer review or novelty certification is claimed. The original target below is retained unchanged.

## Problem statement

Given $`n\ge r`$, take arbitrary base factors $`\bar A,\bar B,\bar C\in\mathbb R^{n\times r}`$, and form $`A,B,C`$ by adding independent Gaussian entries of variance $`\rho^2/n`$, where $`\rho=r^{-q}`$ and $`q>0`$ is fixed. The input is

```math
T=\sum_{j=1}^{r}a_j\otimes b_j\otimes c_j.
```

Does there exist $`k(r)=o(r^2)`$, a polynomial lower bound $`n_0(r)`$, and an explicitly specified ALS or gradient-descent method, initialized randomly, such that for every $`n\ge n_0(r)`$ and $`0<\varepsilon<1`$ it returns $`k`$ summands with

```math
\left\|T-\sum_{i=1}^{k}x_i\otimes y_i\otimes z_i\right\|_F
\le\varepsilon\|T\|_F
```

using polynomially many exact real arithmetic operations in $`n,r,\log(1/\varepsilon)`$, with probability $`1-o_r(1)`$ over the once-drawn smoothed input and at least inverse-polynomial conditional success over initialization? Update rules, initialization, and permitted restarts must be specified. Initial factors must be sampled independently of the input and its unknown factors, apart from an explicitly specified scalar scale normalization and dependence on $`n,r,\rho,\varepsilon`$. The method must optimize the squared residual by alternating block least squares or gradient steps; substituting an algebraic tensor-recovery algorithm does not answer the question. The base-factor quantifier must be preserved rather than replaced by assumptions about the successful trajectory.

## References

Dionysis Arvanitakis, Vaidehi Srinivas, and Aravindan Vijayaraghavan, [*Open Problem: How Much Overparametrization Is Needed for ALS in Tensor Decomposition?*](https://proceedings.mlr.press/v336/arvanitakis26a.html), COLT 2026, PMLR 336, 7105–7110, §2, Open Problem 2 and the following probability clarification. Zhang et al., [*VALG: An Agentic System for ML Theory Research and Demonstrations on COLT 2026 Open Problems*](https://arxiv.org/html/2608.13060v1), §4.1.1, Theorem 4.1 and Discussion.

## Status check — 2026-09-10

Rechecked the [COLT 2026 problem](https://proceedings.mlr.press/v336/arvanitakis26a.html) and [VALG, §4.1.1](https://arxiv.org/html/2608.13060v1), and searched for subquadratic ALS resolutions. VALG explicitly reports only partial progress, with $`k=\Theta(r^{5/3}(\log r)^{5/2})`$, adding scale, interference, balance, smoothing and dimension assumptions and using a proposal/landing/ALS pipeline. It is not a verified solution under every initialization and update convention displayed here; arbitrary base factors remain the decisive unresolved quantifier. No full resolution was located. The source informally motivates well-conditioned factors, but its displayed smoothed model permits arbitrary base factors; this entry preserves that quantifier.

