# AC-04 — Minimal asymptotic rank of the small Coppersmith–Winograd tensor

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because reaching the minimal asymptotic rank for this tensor would force the foundational exponent-two breakthrough; broad importance therefore extends well beyond its fixed small format.  
**Topic:** asymptotic tensor algorithms  
**Last checked:** 2026-09-10  
**Status:** Open  

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
upper bound $`\widetilde R(T)<3.931`$. Searches for “small Coppersmith Winograd
asymptotic rank 2026 3” located that improvement, not equality. Border-rank
results for a fixed tensor power do not alone determine this limit.
**Admitted: no resolution located.**

## Status check — 2026-09-10

Rechecked [Alman–Li, abstract and Theorems 1.2–1.3](https://arxiv.org/html/2605.21738v1), and searched for later small Coppersmith–Winograd asymptotic-rank results. The paper improves the upper bound below 3.931 and confirms that equality with three would imply exponent two. No proof or disproof of that equality was located. An improved upper bound or a border-rank result for one finite power is not a solved portion of this single exact-value target.
