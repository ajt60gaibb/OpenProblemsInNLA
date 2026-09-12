# NR-04 — The nonnegative rank of the nine-point distance matrix

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** hard  
**Importance:** interesting to specialist  
**Rating rationale:** Hard because a single small exact factorization must be constructed or excluded using sharp nonnegative-rank tools; specialist importance reflects its role as a named distance-matrix benchmark.  
**Status:** Solved  
**Area:** exact factorization of Euclidean distance matrices  
**Last checked:** 2026-09-11  

<!-- colbrook-factorization -->
## Resolution — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the exact target.**

The nine-point matrix $`D_{ij}=(i-j)^2`$ has nonnegative rank seven, so no exact six-term nonnegative factorization exists. A polygon-contact argument applied to both factors, together with Sylvester's rank inequality, proves the lower bound; an explicit seven-term integer factorization proves the upper bound.

The complete target is resolved. Its former difficulty rating is historical; the original statement, references and dated audits remain below.

**Primary reference:** [complete authored PDF](../../references/colbrook-factorization-2026-09-11/manuscripts/NR-04_nine_point_distance.pdf), [standalone TeX](../../references/colbrook-factorization-2026-09-11/manuscripts/NR-04_nine_point_distance.tex), **Theorem 1, with Theorem 4 for the lower bound**. [Independent proof review](../../references/colbrook-factorization-2026-09-11/verification/reviews/NR-04-review.md) · [Authorship and submission record](../../references/colbrook-factorization-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-factorization -->

## Context and notation

All factorizations are over the real numbers. For
$`X\in\mathbb R_{\ge0}^{m\times n}`$, define

```math
\mathop{\mathrm{rank}}\nolimits_+(X)=\min\{r\ge0:X=WH,\quad
W\in\mathbb R_{\ge0}^{m\times r},\ H\in\mathbb R_{\ge0}^{r\times n}\}.
```

## Problem statement

Let $`D\in\mathbb R_{\ge0}^{9\times9}`$ have entries
$`D_{ij}=(i-j)^2`$ for $`1\le i,j\le9`$.

### Question

Does there exist an exact factorization
$`D=WH`$ with $`W\in\mathbb R_{\ge0}^{9\times6}`$ and
$`H\in\mathbb R_{\ge0}^{6\times9}`$? Equivalently, is
$`\mathop{\mathrm{rank}}\nolimits_+(D)=6`$ or $`7`$?

## References

Baeckelant, Vandaele, and Gillis,
[*Computing Lower Bounds on the Nonnegative Rank via Non-Convex Optimization Solvers*](https://arxiv.org/html/2605.14058v2),
Appendix A.1, Table 6 and its final paragraph, expressly isolates this case.
Pavel Hrubeš, *On the nonnegative rank of distance matrices*, Information
Processing Letters **112** (2012), 457–461, supplies the upper-bound construction
cited there.

## Status check — 2026-09-10

Rechecked [Baeckelant et al. v2, Appendix A.1, Table 6 and final paragraph](https://arxiv.org/html/2605.14058v2), and searched for later nine-point distance-matrix factorizations. The July 2026 text explicitly retains the gap between six and seven. Its new exact results for orders eleven and twelve do not settle order nine. No six-factor construction or seven-factor lower bound was located.

