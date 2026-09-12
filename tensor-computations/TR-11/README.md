# TR-11 — Generic identifiability of tensors at strictly subcritical ranks

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because the target is a classification across all formats and strictly subcritical ranks, with secant nondefectivity and exceptional families as obstacles; community importance is generic uniqueness of CP factors.  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

## Statement

Let $`d\ge3`$, $`n_1\ge\cdots\ge n_d\ge2`$, and define

```math
r_*={\prod_{i=1}^d n_i\over 1+\sum_{i=1}^d(n_i-1)},\qquad
b=\prod_{i=2}^d n_i-\sum_{i=2}^d(n_i-1).
```

For every integer $`1\le r<r_*`$, a generic rank-$`r`$ tensor in $`\bigotimes_{i=1}^d\mathbb C^{n_i}`$ is conjectured to have a unique expression as a sum of $`r`$ nonzero rank-one tensors, except in these cases:

1. $`n_1>b`$ and $`r\ge b`$.
2. Format $`(4,4,3)`$, rank $`5`$.
3. Format $`(n,n,2,2)`$, rank $`2n-1`$, with $`n\ge2`$.
4. Format $`(4,4,4)`$, rank $`6`$.
5. Format $`(6,6,3)`$, rank $`8`$.
6. Format $`(2,2,2,2,2)`$, rank $`5`$.

A rank-one summand is $`v_1\otimes\cdots\otimes v_d`$. Uniqueness identifies decompositions whose tensor summands differ only by permutation. Generic means outside a proper Zariski-closed subset of the Zariski closure of tensors of rank at most $`r`$, restricted to tensors of actual rank $`r`$. The number $`r_*`$ is a rational dimension-count value, not an assumed actual generic rank.

## Relevance

The conjecture specifies the range in which a generic low-rank tensor model has uniquely recoverable factors, an essential precondition for numerical CP decomposition and component interpretation.

## References

1. L. Chiantini, G. Ottaviani, and N. Vannieuwenhoven, *Effective criteria for specific identifiability of tensors and forms*. [Primary preprint](https://arxiv.org/pdf/1609.00123), §3, Conjecture 6 and Remark 7, p.7. The author journal manuscript numbers these Conjecture 3.4 and Remark 3.5.
2. The same authors, *An Algorithm for Generic and Low-Rank Specific Identifiability of Complex Tensors*, SIAM J. Matrix Anal. Appl. 35 (2014), 1265–1287. [DOI](https://epubs.siam.org/doi/10.1137/140961389); [primary preprint](https://arxiv.org/abs/1403.4157), Theorem 1.1, for the verified bounded-format classification.
3. A. Massarenti and M. Mella, *Bronowski's conjecture and the identifiability of projective varieties*. [January 2024 primary revision](https://arxiv.org/pdf/2210.13524v3), abstract and §§3–4, for later conditional links between identifiability and nondefectivity.

## Status check — 2026-09-10

Rechecked [Chiantini–Ottaviani–Vannieuwenhoven, Conjecture 6 and Remark 7](https://arxiv.org/pdf/1609.00123), including all six exceptions. The source records proof for formats with product of dimensions at most 15000. Targeted searches for later Segre identifiability and classification results found additional nondefectivity/identifiability bounds, but no unrestricted classification. The displayed family therefore has substantive proved cases and an unresolved general remainder; a fresh primary reaffirmation of the entire list was not located.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
