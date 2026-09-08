# TR-13 — Equality of ranks for generic odd-order Hankel tensors

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Last checked:** 2026-09-08

## Statement

Fix an odd integer $m\ge5$ and $n\ge2$. A complex Hankel tensor $H$ of order $m$ and dimension $n$ has entries
$$
H_{i_1\ldots i_m}=h_{i_1+\cdots+i_m-m},\qquad 1\le i_j\le n,
$$
for $h\in\mathbb C^{m(n-1)+1}$. Is there a nonempty Zariski-open subset of this Hankel tensor space on which
$$
R(H)=R_{\rm sym}(H)=\underline R(H)=\underline R_{\rm sym}(H)=R_V(H)?
$$
Here $R$ is the minimum number of arbitrary complex rank-one tensor summands; $R_{\rm sym}$ restricts summands to complex multiples of $v^{\otimes m}$. Each underlined border rank is the least integer $r$ admitting a sequence of complex tensors of the corresponding rank at most $r$ converging entrywise to $H$. $R_V$ further restricts $v$ to
$$
v(a,b)=(a^{n-1},a^{n-2}b,\ldots,b^{n-1}),\quad (a,b)\ne(0,0).
$$
Thus limits defining symmetric border rank stay in the symmetric tensor space; limits defining ordinary border rank need not. Generically $R_V=\lceil(m(n-1)+1)/2\rceil$.

## Relevance

Hankel tensor decompositions encode sums of exponentials used in signal reconstruction. The conjecture compares structured decomposition lengths with the best unconstrained low-rank descriptions.

## References

1. J. Nie and K. Ye, *Hankel Tensor Decompositions and Ranks*, SIAM J. Matrix Anal. Appl. 40 (2019). [DOI](https://epubs.siam.org/doi/10.1137/18M1168285); [author preprint](https://arxiv.org/pdf/1706.03631), §6, Question 6.1 and Conjecture 6.2, p.16; Corollary 3.3 gives the generic Vandermonde rank.
2. L. Qi, *Hankel Tensors: Associated Hankel Matrices and Vandermonde Decomposition*, 2014. [Primary preprint](https://arxiv.org/pdf/1310.5470), §1, equation (1), and §4, Theorem 3, for the structured decomposition background.

## Status check — 2026-09-08

Reference 1's latest arXiv revision, January 28, 2019, explicitly poses this conjecture after the even-order and third-order results. Searches `"Hankel" "Conjecture 6.2"`, `"Hankel tensor" "rank" "odd order" conjecture`, and `"Hankel" "rank" "conjecture" "2026"` found no resolution. Status is supported by the originating paper and a bounded later search, without a fresh 2026 reaffirmation located.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
