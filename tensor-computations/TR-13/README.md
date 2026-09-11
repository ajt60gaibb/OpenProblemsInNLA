# TR-13 — Equality of ranks for generic odd-order Hankel tensors

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because the remaining odd orders require rank lower bounds beyond the proved even-order and cubic mechanisms; specialist importance reflects the restriction to generic Hankel tensors.  
**Last checked:** 2026-09-11  
**Status:** Solved  

<!-- colbrook-recovered-tensors -->
## Resolution — 2026-09-11

**Affirmative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. For every odd $m\ge5$ and $n\ge2$, a nonempty Zariski-open set of complex Hankel tensors has ordinary rank, symmetric rank, ordinary border rank, symmetric border rank and Vandermonde rank all equal to $\lceil(m(n-1)+1)/2\rceil$. A compressed three-slice Koszul flattening gives the ordinary-border-rank lower bound, including arbitrary unstructured limiting sequences; a dominant moment map supplies the matching actual Vandermonde-rank upper bound. Exceptional Hankel tensors and the separate all-tensors question TR-14 are not settled.

[Complete manuscript, Theorem 1 and Sections 2–5](../../references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-13.pdf) · [Standalone TeX](../../references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-13.tex) · [Independent complete-source PASS review](../../references/colbrook-recovered-tensors-2026-09-11/verification/reviews/TR-13-review.md) · [Authorship and provenance](../../references/colbrook-recovered-tensors-2026-09-11/README.md).

The recovered AI-assisted proof passed independent agent review; this is not external human peer review or formal certification. The original target and dated source audit are retained. Difficulty, importance and rating rationale are historical. No novelty or priority claim is made.
<!-- /colbrook-recovered-tensors -->

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

## Status check — 2026-09-10

Rechecked [Nie–Ye, §6, Question 6.1 and Conjecture 6.2](https://arxiv.org/pdf/1706.03631), and searched the conjecture number and later odd-order Hankel-rank literature. The general odd-order target remains conjectural in that source; its even-order and order-three theorems are already excluded here. No later proof or counterexample was located. Status rests on the 2019 primary text plus this bounded search.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
