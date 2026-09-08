# TR-08 — Sharp sparsity threshold for injectivity of a random sparse rectangular matrix

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open problem in a preprint updated 2026-07-08.  
**Last checked:** 2026-09-08  

## Problem statement

Let $k\to\infty$ through multiples of 100, $n_k\ge k^{1+c}$ for fixed $c>0$, and $1\le s_k\le k$. Independently for each column of $M_k\in\mathbb R^{k\times n_k}$, choose $s_k$ distinct row locations uniformly and put independent signs $\pm1/\sqrt{s_k}$ there. Independently select a uniform $k/100$-element column set $I_k$.

Determine necessary and sufficient asymptotic conditions on $s_k$ for the existence of an absolute $a>0$ such that

$$
\Pr\{\sigma_{\min}((M_k)_{:I_k})\ge a\}=1-o(1).
$$

Probability includes both random constructions. The requested threshold concerns a lower singular-value bound, not an upper distortion estimate.

## Reference

Huang, Rudelson, and Tikhomirov, [*Well-Invertible Column Subsets of Sparse Matrices Are Rare*](https://arxiv.org/html/2607.05384v2), §7, Problem 7.2.

## Status check

Searches included `"Optimal OSI sparsity" "2026"` and the paper title with `threshold`. No sharp threshold result was located. A sufficient condition from a two-sided embedding theorem would not on its own establish necessity here.
