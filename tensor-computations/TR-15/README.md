# TR-15 — Nonnegative H-eigenvalue inheritance from odd-order Hankel tensors

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because odd-order H-eigenvalue positivity lacks the even-order polynomial-positivity argument; specialist importance lies in transferring spectral certificates within Hankel representations.  
**Last checked:** 2026-09-11  
**Status:** Solved  

<!-- colbrook-unclaimed -->
## Resolution — 2026-09-11

**Negative resolution.** Matthew J. Colbrook's [complete manuscript, Counterexample proposition and proof](../../references/colbrook-unclaimed-2026-09-11/manuscripts/TR-15.md) disproves the universal conjecture with $m=3$, $q=2$, $n=2$ and the common generating vector $h=(2,0,1,0,2,0,-1)$. Every real H-eigenvalue of the order-three, dimension-three tensor $A$ is strictly positive, whereas the order-six, dimension-two tensor $B$ has the exact H-eigenpair $(-1,(0,1))$. The manuscript also proves that $A$ has a real H-eigenpair, so its premise is nonvacuous. The counterexample meets the original odd-lower-order assumptions; it does not contradict the separate even-lower-order theorem or results requiring a positive-semidefinite associated Hankel matrix.

The complete source passed [independent Codex-agent proof review](../../references/colbrook-unclaimed-2026-09-11/verification/reviews/TR-15-review.md). [Authorship, AI assistance and verification record](../../references/colbrook-unclaimed-2026-09-11/README.md). No external human peer review or formal verification is asserted. The original target below is retained verbatim; the difficulty, importance and rating rationale above are historical. This entry no longer contributes to the open count.

[Manuscript PDF](../../references/colbrook-unclaimed-2026-09-11/manuscripts/TR-15.pdf). 
<!-- /colbrook-unclaimed -->

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

## Status check — 2026-09-10

Rechecked the [Ding–Qi–Wei journal text, final §4](https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf), and searched for proofs or counterexamples to the third inheritance property. The source explicitly leaves odd lower order unresolved; its even-lower-order result lies outside the displayed target. Complete or strong Hankel hypotheses would be additional restrictions. No later resolution was located; this remains a bounded historical-source check.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
