# AC-02 — Exact bilinear rank of the $`3\times3`$ matrix product

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because the exact rank of this small multiplication tensor remains a decades-old barrier despite extensive algorithm searches; community importance concerns recursive matrix multiplication and bilinear algorithm design.  
**Topic:** small matrix multiplication algorithms  
**Last checked:** 2026-11-27

**Status:** Partially resolved

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
lower bound over $`\mathbb F_2`$. The later results below give a complex lower
bound of 21 and determine the rank over $`\mathbb F_2`$.

## Status check — 2026-09-10

Rechecked [Sun’s rank-23 construction](https://arxiv.org/abs/2604.27645) and [Alman–Li, §1](https://arxiv.org/html/2605.21738v1), which explicitly identifies both exact rank and border rank of the 3×3 product as unresolved. Searches for 22-product complex bilinear algorithms found no qualifying construction or matching lower bound. Fewer additions at rank 23 and finite-field lower bounds do not settle this complex-field minimum.

## Reviewed research submission — 14 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation and submission record](../../references/holden-ac-2026-09-14/README.md).

Reviewed results cover fixed-support calculations, the Sun four-block conditional obstruction and two five-block examples. Unrestricted complex rank remains undetermined. Missing continuation checkers prevent certification of its larger noncompletion claims; these are excluded from the passing audit.

[Report](../../references/holden-ac-2026-09-14/AC-02-submission.pdf) · [Independent AI-agent audit and limitations](../../references/holden-ac-2026-09-14/verification/review-ac01-ac02.md). AI assistance disclosed; no external human review, formal verification or Lean checks for this submission.

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

The authors supply a Lean formalization and describe its audit procedure in
§3. The October 6 check reviewed the paper's statements and scope.

## Literature update — 2026-11-27

Andrey Ivanov proves that every exact bilinear algorithm for this product over
an arbitrary field $`K`$ has at least 21 terms. The Lean statement takes
arbitrary $`K`$-linear forms $`a_t,b_t`$ and output matrices $`W_t`$ indexed by a
finite set, with $`AB=\sum_t a_t(A)b_t(B)W_t`$ for all pairs $`A,B`$. Setting
$`K=\mathbb C`$ gives precisely the admissible decompositions in the problem
statement. Along with the 23-product upper bound, this gives $`21\le r\le23`$,
improving Bläser's lower bound of 19.
Determining which of 21, 22 and 23 is the exact complex rank remains open.
[Ivanov's pinned theorem](https://github.com/AIV5/mmrank21/blob/cb1557b7ea80ea66fae4714628663d8c1df7a48d/Solution.lean).

The audit compared `MMRank.Palomar.lower_bound` with the displayed problem
and reviewed Palomar's successful replay of commit
`cb1557b7ea80ea66fae4714628663d8c1df7a48d` on October 12, registered October 13.
The replay compared the proof with the Mathlib-only statement using Lean
`v4.35.0-rc2`, with `propext`, `Classical.choice` and `Quot.sound` as the only
permitted axioms. Verification here consisted of inspecting the theorem and
public replay record. [Palomar entry](https://palomar-registry.org/entry?id=PALOMAR-2026-10-13-000009&version=1) · [Mechanical report](https://data.palomar-registry.org/evidence/PALOMAR-2026-10-13-000009-v1/d7fb2a4a49eead03d7cf3a406c9caed9905363aac47ff064d8064eb09049e779/mechanical-report.json).

Tejasvi Singh Tomar establishes exact rank 23 over $`\mathbb F_2`$ and for
integer coefficients by reduction modulo 2. Arbitrary complex coefficients
do not permit that reduction. [Tomar, arXiv:2610.11823v3](https://arxiv.org/abs/2610.11823v3).
