# AC-05 — Strassen's asymptotic rank conjecture for tight tensors

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because it predicts minimal asymptotic complexity for every concise tight tensor; broad importance follows from consequences for matrix multiplication and exponential-time combinatorial algorithms.  
**Topic:** complexity of structured tensor powers  
**Last checked:** 2026-09-10  
**Status:** Open  

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
(2026), Conjecture 1, retains the tight/concise formulation. Searches for
“asymptotic rank conjecture proved 2026” found no resolution. Numerical evidence
is not a proof. **Admitted: no resolution located.**

## Status check — 2026-09-10

Rechecked [Lee, Conjecture 1](https://arxiv.org/html/2601.08119v1) and [Björklund–Kaski](https://arxiv.org/abs/2310.11926), then searched for 2026 proofs and counterexamples. The tight/concise asymptotic-rank formulation remains explicitly conjectural. Its incompatibility with the Set Cover Conjecture is conditional and does not refute it. No unconditional full resolution was located; numerical rank estimates do not prove the universal limit.
