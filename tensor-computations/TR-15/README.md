# TR-15 — Nonnegative H-eigenvalue inheritance from odd-order Hankel tensors

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Last checked:** 2026-09-08

## Statement

For every odd $m\ge3$, integer $q\ge2$, dimension $n\ge2$, and vector $h\in\mathbb R^{qm(n-1)+1}$, define Hankel tensors $A$ and $B$ with this same generating vector. Their orders and dimensions are
$$
\operatorname{order}(A)=m,\quad\dim(A)=q(n-1)+1,
\qquad \operatorname{order}(B)=qm,\quad\dim(B)=n.
$$
An order-$s$, dimension-$N$ Hankel tensor has entry $h_{i_1+\cdots+i_s-s}$, with each index in $\{1,\ldots,N\}$.

For a real order-$s$ tensor $C$, an H-eigenvalue is a real $\lambda$ admitting a real nonzero vector $x$ such that, for every $i$,
$$
\sum_{i_2,\ldots,i_s=1}^N C_{i i_2\cdots i_s}x_{i_2}\cdots x_{i_s}
=\lambda x_i^{s-1}.
$$
Conjecture: if $A$ has no negative H-eigenvalues, then $B$ has no negative H-eigenvalues.

## Relevance

The question transfers a spectral positivity certificate between different Hankel representations of the same data, relevant to structured tensor eigenvalue computation and polynomial positivity.

## References

1. W. Ding, L. Qi, and Y. Wei, *Inheritance properties and sum-of-squares decomposition of Hankel tensors: theory and algorithms*, BIT Numer. Math. 57 (2017), 169–190. [DOI](https://doi.org/10.1007/s10543-016-0622-0); [author PDF](https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf), final §4, “The third inheritance property of Hankel tensors,” concluding conjecture; §2 gives order/dimension conventions.
2. L. Qi, *Hankel Tensors: Associated Hankel Matrices and Vandermonde Decomposition*, 2014. [Primary preprint](https://arxiv.org/pdf/1310.5470), §5, concerning H-eigenvalues and complete Hankel tensors.

## Status check — 2026-09-08

Reference 1 proves the corresponding inheritance with even lower order and leaves the odd-order case conjectural. Searches `"Hankel" "third inheritance" counterexample`, `"tensor" "inheritance" "conjecture" Hankel proof`, and `"Hankel" "inheritance" "2026" conjecture` located no resolution. Results under stronger assumptions such as complete Hankel structure do not establish this statement. This is a bounded historical-source check.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
