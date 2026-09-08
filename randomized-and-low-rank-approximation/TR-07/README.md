# TR-07 — Random column subsets of arbitrary fixed-sparsity matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open conjecture in a preprint updated 2026-07-08.  
**Last checked:** 2026-09-08  

## Problem statement

Fix an integer $s\ge2$ and $C\ge1$. Suppose $r_k\le k$, $k/r_k\to C$, and $n_k/r_k\to\infty$. For every deterministic sequence $M_k\in\{-1,0,1\}^{k\times n_k}$ with exactly $s$ nonzero entries per column, and a uniformly random $r_k$-element column set $I_k$, prove or disprove

$$
\forall\eta>0,\qquad
\Pr\{\sigma_{\min}((M_k)_{:I_k})>\eta\}\longrightarrow0.
$$

Here $\sigma_{\min}(B)=\inf_{\|x\|_2=1}\|Bx\|_2$. There is no hypothesis controlling intersections of column supports.

## Reference

Han Huang, Mark Rudelson, and Konstantin Tikhomirov, [*Well-Invertible Column Subsets of Sparse Matrices Are Rare*](https://arxiv.org/html/2607.05384v2), §7, Conjecture 7.1; compare Theorem 1.3 for the additional structural hypothesis in the proved result.

## Status check

Searches included `"unrestricted deterministic sparse sketches" conjecture` and the exact paper title with `2026`. No subsequent resolution was located. The paper’s disproof of a particular SparseStack conjecture does not establish its own unrestricted deterministic conjecture.
