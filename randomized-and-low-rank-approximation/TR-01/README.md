# TR-01 — Optimal dimension for a rerandomized Hadamard embedding

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because two structured randomizations must remove the embedding logarithm uniformly over subspaces; community impact is fast sketching for least squares and low-rank methods.  
**Status:** Open  
**Last checked:** 2026-09-10  

## Problem statement

Let $n$ be a power of two, $1\le r\le n$, and $0<\varepsilon<1/2$. Let $F$ be the normalized Walsh–Hadamard matrix, let $D_1,D_2$ have independent Rademacher diagonal entries, and let $S\in\mathbb R^{n\times k}$ select a uniformly random $k$-element subset of coordinates, independently. Set

$$
\Omega=\sqrt{n/k}\,D_1FD_2FS.
$$

Does a universal $C>0$ exist such that, for every fixed $r$-dimensional subspace $V\subseteq\mathbb R^n$, choosing $k=\min\{n,\lceil Cr/\varepsilon^2\rceil\}$ gives

$$
\Pr\left\{(1-\varepsilon)\|x\|_2^2\le
\|\Omega^Tx\|_2^2\le(1+\varepsilon)\|x\|_2^2
\text{ for every }x\in V\right\}\ge0.99?
$$

This fixes normalization, sampling without replacement, and a constant success probability in the workshop question. Results for a single randomization, three randomizations, or independently sampled sparse sketches do not establish this statement.

## References

Amsel et al., [*Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop*](https://arxiv.org/html/2602.05394v3), §5.3, Definition 5.3 and Problem 5.6. For the single-round baseline, Joel A. Tropp, [*Improved Analysis of the Subsampled Randomized Hadamard Transform*](https://arxiv.org/abs/1011.1595), *Advances in Adaptive Data Analysis* 3 (2011), 115–126, Theorem 3.1.

## Status check

Searches included `"rerandomized SRHT" counterexample`, `"rerandomized" "subspace" Hadamard`, and `"Hadamard" "two" "2026" embedding conjecture`. No resolution of the displayed two-round assertion was located. The September 2026 SparseStack result in the [screening notes](../../references/SCREENED-OUT.md#screened-items-that-are-not-counted) concerns another distribution.

## Audit — 2026-09-10

Rechecked [workshop Problem 5.6](https://arxiv.org/html/2602.05394v3). The precise two-round Hadamard distribution remains unproved there. Rerandomized-Hadamard and later embedding searches found no resolution; guarantees for independent sparse entries or additional randomizations do not settle this distribution.
