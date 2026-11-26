# AC-04 — Minimal asymptotic rank of the small Coppersmith–Winograd tensor

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because reaching the minimal asymptotic rank for this tensor would force the foundational exponent-two breakthrough; broad importance therefore extends well beyond its fixed small format.  
**Topic:** asymptotic tensor algorithms  
**Last checked:** 2026-11-26  
**Status:** Solved  

## Negative resolution — 24 November 2026

The asymptotic rank of the displayed tensor is strictly greater than three.
Its flattening rank is three and is multiplicative under the grouped tensor
powers, giving the lower bound three. Equality would force the complex
matrix multiplication exponent to be two by Theorem 1.2 of
[Alman and Li, *Asymptotic Rank Speedup Theorems, Revisited*](https://arxiv.org/html/2605.21738v1).
The tensor in that theorem is the displayed small Coppersmith–Winograd
tensor with parameter two. The November exact exponent is nine fourths,
so the equality is impossible. This update checked the reduction against
the original target and reviewed the verification record for the exponent.
The deduction settles the equality question and leaves the exact value
of the asymptotic rank undetermined.
[Exponent result and verification](../AC-01/README.md#lean-proof-and-verification-evidence).

## Context and notation

Over $`\mathbb C`$, the tensor rank $`R(T)`$ is the minimum number of pure tensors in an exact sum for $`T`$.

## Problem statement

Let $`e_0,e_1,e_2`$ be the standard basis of $`\mathbb C^3`$ and set

```math
T=\sum_{i=1}^{2}(e_0\otimes e_i\otimes e_i+
 e_i\otimes e_0\otimes e_i+e_i\otimes e_i\otimes e_0).
```

For a tensor $`S`$, define $`\widetilde R(S)=\lim_{k\to\infty} R(S^{\otimes k})^{1/k}`$, grouping corresponding factors when taking powers.
Is $`\widetilde R(T)=3`$?

## Why it matters

This explicitly studied tensor offers a route to exponent
two for matrix multiplication. It is not counted separately for other values
of its size parameter.

## References and status

Bläser, [2013](https://theoryofcomputing.org/articles/gs005/gs005.pdf),
Problem 9.8. Alman–Li, [2026](https://arxiv.org/abs/2605.21738),
Theorems 1.2–1.3, relates the target to $`\omega=2`$ and establishes the partial
upper bound $`\widetilde R(T)<3.931`$.

## Status check — 2026-09-10

Rechecked [Alman–Li, abstract and Theorems 1.2–1.3](https://arxiv.org/html/2605.21738v1), and searched for later small Coppersmith–Winograd asymptotic-rank results. The paper improves the upper bound below 3.931 and confirms that equality with three would imply exponent two. No proof or disproof of that equality was located. An improved upper bound or a border-rank result for one finite power is not a solved portion of this single exact-value target.

## Reviewed research submission — 14 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation and submission record](../../references/holden-ac-2026-09-14/README.md).

Theorems 3.1 and 4.2 give $`\widetilde R(T)<3.896914`$; later sections prove local rigidity. The separately reviewed [AC-01 report](../../references/holden-ac-2026-09-14/AC-01-submission.pdf), Section 8, strengthens the bound to $`3.876919161`$. Neither settles equality with three.

[Report](../../references/holden-ac-2026-09-14/AC-04-submission.pdf) · [Independent AI-agent audit and limitations](../../references/holden-ac-2026-09-14/verification/review-ac03-ac04.md). AI assistance was disclosed. This submission received an informal AI-agent audit.
