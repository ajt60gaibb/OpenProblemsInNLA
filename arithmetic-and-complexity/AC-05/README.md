# AC-05 — Strassen's asymptotic rank conjecture for tight tensors

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because it predicts minimal asymptotic complexity for every concise tight tensor; broad importance follows from consequences for matrix multiplication and exponential-time combinatorial algorithms.  
**Topic:** complexity of structured tensor powers  
**Last checked:** 2026-11-26  
**Status:** Solved  

## Negative resolution — 24 November 2026

The two-by-two matrix multiplication tensor is a counterexample. Label the
three factors by $`(i,j)`$, $`(j,k)`$ and $`(k,i)`$, with
$`i,j,k\in\{0,1\}`$. Each flattening has rank four because its four rows
have nonempty disjoint support. The three label functions
$`i+2j`$, $`-2j+4k`$ and $`-4k-i`$ are injective on their respective pairs and
sum to zero on every support triple. This checks conciseness and tightness
in the displayed formulation with $`d=4`$.

The asymptotic rank of this tensor is $`2^{9/4}>4`$. Corollary 1.2 of
OpenAI's [*The matrix multiplication exponent is nine
fourths*](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf)
gives asymptotic rank $`n^{9/4}`$ for the square multiplication tensor of
side length $`n`$. The independent audit checked this rank formula in Lean
against a separately written definition. This catalog checked the
counterexample's hypotheses above directly.
[Audit, row G3c](https://carlostoledo.co/omega/).

## Context and notation

Over $`\mathbb C`$, the tensor rank $`R(T)`$ is the minimum number of pure tensors in an exact sum for $`T`$.

## Problem statement

A tensor $`T\in(\mathbb C^d)^{\otimes3}`$ is *concise* if each of its
three matrix flattenings has rank $`d`$. It is *tight* if some choice of bases
admits injective functions $`a,b,c:\{1,\ldots,d\}\to\mathbb Z`$ with
$`a(i)+b(j)+c(k)=0`$ whenever the coefficient $`T_{ijk}`$ is nonzero. Is

```math
\lim_{m\to\infty}R(T^{\otimes m})^{1/m}=d
```

for every positive integer $`d`$ and every concise tight $`T`$? Tensor powers use
corresponding-factor grouping; rank is over $`\mathbb C`$.

## Why it matters

This is a structural conjecture about many bilinear
computations, beyond the single matrix-multiplication family. [AC-04](../AC-04/README.md) is a named special tensor
with independent literature treatment; this universal statement is not its
equivalent reformulation.

## References and status

A. Björklund and P. Kaski,
[*The Asymptotic Rank Conjecture and the Set Cover Conjecture are not Both
True*](https://arxiv.org/abs/2310.11926), Conjecture 3 and §2.3, states the
conjecture and gives a conditional consequence, not a refutation. K. Lee,
[*Asymptotic rank bounds: a numerical census*](https://arxiv.org/abs/2601.08119)
(2026), Conjecture 1, records the tight/concise formulation.

## Status check — 2026-09-10

Rechecked [Lee, Conjecture 1](https://arxiv.org/html/2601.08119v1) and [Björklund–Kaski](https://arxiv.org/abs/2310.11926), then searched for 2026 proofs and counterexamples. The tight/concise asymptotic-rank formulation remains explicitly conjectural. Its incompatibility with the Set Cover Conjecture is conditional and does not refute it. No unconditional full resolution was located; numerical rank estimates do not prove the universal limit.

## Reviewed research submission — 14 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation](../../references/holden-ac-2026-09-14/README.md) · [Report](../../references/holden-ac-2026-09-14/AC-05-submission.pdf) · [Independent AI audit](../../references/holden-ac-2026-09-14/verification/review-ac05-ac06.md).

Theorems 3.2–9.3 give scoped power classifications and finite lower bounds.
AI assistance was disclosed. This submission received an informal AI-agent
audit, limited to the stated results.
