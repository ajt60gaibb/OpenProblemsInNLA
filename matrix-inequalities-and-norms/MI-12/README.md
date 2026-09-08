# MI-12 — Marcus's inequality for the permanent of block permanents

**Difficulty:** extreme  
**Importance:** interesting to specialist  
**Status:** explicit conjectured inequality; no later resolution located  
**Last checked:** 2026-09-08

For a square matrix $C$ of order $r$, write
$$
\operatorname{per}C=\sum_{\sigma\in S_r}\prod_{i=1}^r c_{i,\sigma(i)}.
$$
Let $m,k\ge2$ be arbitrary integers and let $A\in\mathbb C^{mk\times mk}$ be Hermitian positive semidefinite. Partition $A$ into an $m\times m$ array of $k\times k$ blocks $A_{ij}$, and form
$$
G=(g_{ij})_{i,j=1}^m,\qquad g_{ij}=\operatorname{per}(A_{ij}).
$$
Must
$$
\operatorname{per}A\ge\operatorname{per}G
$$
always hold?

## Relevance
 This asks how a costly matrix polynomial behaves under block aggregation by the same polynomial. It is a precise constraint on hierarchical permanent computation for PSD matrices; positivity is assumed for the whole matrix, not separately for off-diagonal blocks.

## References

- I. M. Wanless, *Lieb's permanental dominance conjecture* (2022), Conjecture 3 and the following paragraph ([primary manuscript](https://arxiv.org/pdf/2202.01867)).
- F. Zhang, *An update on a few permanent conjectures*, Special Matrices 4 (2016), 305–316, discussion of Marcus's permanent-of-permanents conjecture ([primary manuscript](https://arxiv.org/pdf/1608.02844); [journal](https://doi.org/10.1515/spma-2016-0030)).
- E. H. Lieb, *Proofs of some Conjectures on Permanents*, Journal of Mathematics and Mechanics 16 (1966), 127–134, the two-block inequality ([publisher's first page](https://iumj.s3-us-west-2.amazonaws.com/abstracts/16008_abs.pdf)).

## Status check — 2026-09-08
 Wanless records this inequality as open and identifies Lieb's proof for $m=2$. Searches for “Marcus conjecture”, “permanent of permanents”, “block permanents”, “proof”, and 2025–2026 found no general resolution. This entry is specifically the inequality component: some historical formulations additionally conjecture an equality characterization. The trivial block sizes $m=1$ and $k=1$ are omitted, and no unqualified equality characterization is imported. Lieb's general permanental dominance conjecture would imply this assertion, but this is a separately stated historical conjecture.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
