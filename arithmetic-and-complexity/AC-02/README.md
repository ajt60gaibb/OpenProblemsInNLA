# AC-02 — Exact bilinear rank of the $`3\times3`$ matrix product

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because the exact rank of this small multiplication tensor remains a decades-old barrier despite extensive algorithm searches; community importance concerns recursive matrix multiplication and bilinear algorithm design.  
**Topic:** small matrix multiplication algorithms  
**Last checked:** 2026-10-06  
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
lower bound over $`\mathbb F_2`$. Rudich and Rousseau's October preprint,
discussed below, raises the finite-field lower bound to 22; it does not establish
the same lower bound over $`\mathbb C`$. Searches for complex bilinear
algorithms and matching lower bounds found no determination of the exact
complex rank. **Admitted: no resolution located.**

## Status check — 2026-09-10

Rechecked [Sun’s rank-23 construction](https://arxiv.org/abs/2604.27645) and [Alman–Li, §1](https://arxiv.org/html/2605.21738v1), which explicitly identifies both exact rank and border rank of the 3×3 product as unresolved. Searches for 22-product complex bilinear algorithms found no qualifying construction or matching lower bound. Fewer additions at rank 23 and finite-field lower bounds do not settle this complex-field minimum.

## Reviewed research submission — 14 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation and submission record](../../references/holden-ac-2026-09-14/README.md).

Reviewed results cover fixed-support calculations, the Sun four-block conditional obstruction and two five-block examples. Unrestricted complex rank remains undetermined. Missing continuation checkers prevent certification of its larger noncompletion claims; these are excluded from the passing audit.

**Status: Open.** [Report](../../references/holden-ac-2026-09-14/AC-02-submission.pdf) · [Independent AI-agent audit and limitations](../../references/holden-ac-2026-09-14/verification/review-ac01-ac02.md). AI assistance disclosed; no external human review, formal verification or Lean checks. Original target and prior-source credit retained.

## Literature update — 2026-10-06

Isaac Rudich and Louis-Martin Rousseau, [*Lower Bound of 22 for 3x3 Matrix
Multiplication over the Integers*](https://arxiv.org/abs/2610.01639v1),
arXiv:2610.01639v1, submitted 1 October 2026, reports in
[§1](https://arxiv.org/html/2610.01639v1#S1) that the bilinear rank of the
$`3\times3`$ matrix product over $`\mathbb F_2`$ is at least 22.
[§3, displayed theorem (1)](https://arxiv.org/html/2610.01639v1#S3),
`recursive_algorithm_multiplications_at_least_22`, gives the corresponding
lower bound for algorithms with integer constants that work on square matrix
blocks of every size. Sections 3–4 specify this model and the reduction from
integer-coefficient algorithms to decompositions over $`\mathbb F_2`$.

This advances the finite-field and integer-coefficient problems, where the
lower bound 22 and upper bound 23 still differ. It does not establish a lower
bound of 22 over $`\mathbb C`$: arbitrary complex coefficients cannot in general
be reduced modulo 2. The exact complex bilinear rank asked for here remains
undetermined, and **Status: Open** is retained. The authors supply a Lean
formalization and describe its audit procedure in §3; this literature update
reviewed the paper's statements and scope but did not rerun Lean or audit the
formalization.
