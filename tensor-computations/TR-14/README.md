# TR-14 — Comon's exact-rank conjecture for Hankel tensors

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Last checked:** 2026-09-08

## Statement

For every $m\ge3$, $n\ge2$, and $h\in\mathbb C^{m(n-1)+1}$, form the symmetric tensor
$$
H_{i_1\ldots i_m}=h_{i_1+\cdots+i_m-m},\qquad 1\le i_j\le n.
$$
Is $R(H)=R_{\rm sym}(H)$ always true? Here $R(H)$ is the least integer $r\ge0$ admitting
$$
H=\sum_{j=1}^r u_{j,1}\otimes\cdots\otimes u_{j,m},\quad u_{j,k}\in\mathbb C^n,
$$
whereas $R_{\rm sym}(H)$ is the least $r$ admitting $H=\sum_{j=1}^r c_jv_j^{\otimes m}$, with $c_j\in\mathbb C$ and $v_j\in\mathbb C^n$. Empty sums represent zero. No genericity or Vandermonde restriction is imposed.

## Relevance

This would justify symmetry-preserving decomposition lengths for every Hankel tensor, including exceptional data. Such structure appears in harmonic retrieval and structured tensor factorization.

## References

1. J. Nie and K. Ye, *Hankel Tensor Decompositions and Ranks*, SIAM J. Matrix Anal. Appl. 40 (2019). [DOI](https://epubs.siam.org/doi/10.1137/18M1168285); [primary preprint](https://arxiv.org/pdf/1706.03631), §6, Conjecture 6.3, p.16.
2. L. Qi, *Hankel Tensors: Associated Hankel Matrices and Vandermonde Decomposition*, 2014. [Primary preprint](https://arxiv.org/pdf/1310.5470), §1, equation (1), and §4, Theorem 3, for Hankel structure and decomposition.

## Status check — 2026-09-08

Nie and Ye formulate this restricted conjecture after explicitly acknowledging Shitov's counterexample to the unrestricted symmetric-tensor conjecture. Searches `"Hankel" "Conjecture 6.3"`, `"Hankel" "Comon" "counterexample"`, and `"Hankel tensors" ranks conjectures solved` located no solution. No later primary reaffirmation was located; the dated conclusion is bounded by this search.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
