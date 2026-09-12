# TR-14 — Comon's exact-rank conjecture for Hankel tensors

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because exceptional Hankel tensors require a uniform comparison of structured and unrestricted exact decompositions; specialist importance reflects this particular structured tensor class.  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

## Statement

For every $`m\ge3`$, $`n\ge2`$, and $`h\in\mathbb C^{m(n-1)+1}`$, form the symmetric tensor

```math
H_{i_1\ldots i_m}=h_{i_1+\cdots+i_m-m},\qquad 1\le i_j\le n.
```

Is $`R(H)=R_{\rm sym}(H)`$ always true? Here $`R(H)`$ is the least integer $`r\ge0`$ admitting

```math
H=\sum_{j=1}^r u_{j,1}\otimes\cdots\otimes u_{j,m},\quad u_{j,k}\in\mathbb C^n,
```

whereas $`R_{\rm sym}(H)`$ is the least $`r`$ admitting $`H=\sum_{j=1}^r c_jv_j^{\otimes m}`$, with $`c_j\in\mathbb C`$ and $`v_j\in\mathbb C^n`$. Empty sums represent zero. No genericity or Vandermonde restriction is imposed.

## Relevance

This would justify symmetry-preserving decomposition lengths for every Hankel tensor, including exceptional data. Such structure appears in harmonic retrieval and structured tensor factorization.

## References

1. J. Nie and K. Ye, *Hankel Tensor Decompositions and Ranks*, SIAM J. Matrix Anal. Appl. 40 (2019). [DOI](https://epubs.siam.org/doi/10.1137/18M1168285); [primary preprint](https://arxiv.org/pdf/1706.03631), §6, Conjecture 6.3, p.16.
2. L. Qi, *Hankel Tensors: Associated Hankel Matrices and Vandermonde Decomposition*, 2014. [Primary preprint](https://arxiv.org/pdf/1310.5470), §1, equation (1), and §4, Theorem 3, for Hankel structure and decomposition.

## Status check — 2026-09-10

Rechecked [Nie–Ye, Conjecture 6.3, Corollary 4.3 and Theorem 5.4](https://arxiv.org/pdf/1706.03631), and searched for later Hankel Comon proofs and counterexamples. Generic even-order and order-three Hankel tensors are proved cases of the displayed universal equality; exceptional tensors and the remaining orders are not settled by those results. The paper already accounts for Shitov’s unrestricted counterexample. No later full resolution was located.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
