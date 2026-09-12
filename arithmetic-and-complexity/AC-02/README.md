# AC-02 — Exact bilinear rank of the $`3\times3`$ matrix product

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because the exact rank of this small multiplication tensor remains a decades-old barrier despite extensive algorithm searches; community importance concerns recursive matrix multiplication and bilinear algorithm design.  
**Topic:** small matrix multiplication algorithms  
**Last checked:** 2026-09-10  
**Status:** Open  

## Problem statement

Determine the least integer $`r`$ for which there are complex
coefficients $`u_{t,ij},v_{t,ij},w_{ij,t}`$ satisfying, for every pair of complex
$`3\times3`$ matrices,

```math
(AB)_{ij}=\sum_{t=1}^{r} w_{ij,t}
 \left(\sum_{a,b=1}^{3}u_{t,ab}A_{ab}\right)
 \left(\sum_{c,d=1}^{3}v_{t,cd}B_{cd}\right).
```

Scalar linear combinations are free in this bilinear-rank model. The classical
upper bound is 23; deciding whether 22 products suffice is part of determining
the exact minimum. Algorithms mixing entries of both inputs within a factor
are outside this specified model.

## Why it matters

Such identities can be applied recursively to matrix blocks.

## References and status

Bläser, [2013](https://theoryofcomputing.org/articles/gs005/gs005.pdf),
§1 and Example 5.10. Y. Sun, [*An Exact 56-Addition, Rank-23 Scheme for General
3×3 Matrix Multiplication*](https://arxiv.org/abs/2604.27645) (2026), gives another
23-product scheme. C. Wang, [*Automated Lower Bounds for Bilinear Complexity
over Finite Fields*](https://arxiv.org/abs/2603.07280), v10 (2026), improves a
lower bound over $`\mathbb F_2`$; that is not a complex-field resolution. Searches
for “rank 22 matrix multiplication 2026 proof” found no qualifying algorithm
or matching lower bound. **Admitted: no resolution located.**

## Status check — 2026-09-10

Rechecked [Sun’s rank-23 construction](https://arxiv.org/abs/2604.27645) and [Alman–Li, §1](https://arxiv.org/html/2605.21738v1), which explicitly identifies both exact rank and border rank of the 3×3 product as unresolved. Searches for 22-product complex bilinear algorithms found no qualifying construction or matching lower bound. Fewer additions at rank 23 and finite-field lower bounds do not settle this complex-field minimum.
