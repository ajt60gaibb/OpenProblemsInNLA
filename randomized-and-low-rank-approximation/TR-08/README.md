# TR-08 — Sharp sparsity threshold for injectivity of a random sparse rectangular matrix

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because a sharp lower-singular-value threshold needs both necessity and sufficiency; community impact is the sparsity cost of reliable randomized embeddings.  
**Status:** Open  
**Last checked:** 2026-09-12  

## Problem statement

Let $`k\to\infty`$ through multiples of 100, $`n_k\ge k^{1+c}`$ for fixed $`c>0`$, and $`1\le s_k\le k`$. Independently for each column of $`M_k\in\mathbb R^{k\times n_k}`$, choose $`s_k`$ distinct row locations uniformly and put independent signs $`\pm1/\sqrt{s_k}`$ there. Independently select a uniform $`k/100`$-element column set $`I_k`$.

Determine necessary and sufficient asymptotic conditions on $`s_k`$ for the existence of an absolute $`a>0`$ such that

```math
\Pr\{\sigma_{\min}((M_k)_{:I_k})\ge a\}=1-o(1).
```

Probability includes both random constructions. The requested threshold concerns a lower singular-value bound, not an upper distortion estimate.

## Precision of the target

A complete resolution should give an explicit asymptotic criterion on the sparsity sequence $`(s_k)`$ that is equivalent to the displayed probability bound for some fixed positive $`a`$. Separate necessary and sufficient estimates are partial progress whenever a gap between them leaves this property undecided. There is no blanket allowance to ignore constant or logarithmic factors: they need to be resolved insofar as they affect whether the property holds. Optimizing the numerical value of $`a`$ is not required.

The paragraph following Problem 7.2 in the source suggests a natural intermediate goal: establish whether there is a critical logarithmic exponent $`\alpha_*>0`$ and determine its value. The proposed separation is failure of the displayed property for $`s_k=O((\log k)^{\alpha_*-\varepsilon})`$ and success for $`s_k=\Omega((\log k)^{\alpha_*+\varepsilon})`$, for every fixed $`\varepsilon>0`$ in the admissible sparsity range. Such a result need not settle the behavior at $`s_k=(\log k)^{\alpha_*+o(1)}`$, including possible constant or $`\log\log k`$ corrections. It is therefore a milestone toward the full target, rather than a replacement for it; existence of such an exponent is not assumed.

## Reference

Huang, Rudelson, and Tikhomirov, [*Well-Invertible Column Subsets of Sparse Matrices Are Rare*](https://arxiv.org/html/2607.05384v2), §7, Problem 7.2.

## Status check

Searches included `"Optimal OSI sparsity" "2026"` and the paper title with `threshold`. No sharp threshold result was located. A sufficient condition from a two-sided embedding theorem would not on its own establish necessity here.

## Audit — 2026-09-10

Rechecked [Problem 7.2](https://arxiv.org/html/2607.05384v2) and [Tikhomirov's later paper](https://arxiv.org/html/2607.23017v1), which uses different aspect-ratio and randomness regimes. Threshold and sparse-rectangular-matrix searches found no sharp criterion for this fixed-column-sparsity model. A sufficient embedding result alone does not determine the target.

## Clarification — 2026-09-12

Following [issue #150](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/150), rechecked Problem 7.2 and its following paragraph and made the requested precision explicit. This is a clarification of the original target, not a new literature-wide status audit or a resolution. The ID, matrix model, probability bound and Open status are unchanged.
