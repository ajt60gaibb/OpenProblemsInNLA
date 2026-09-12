# PF-04 — The maximum cp-rank in order six

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because sharp cp-rank control is still missing for the remaining order-six boundary configurations; community importance is the size of exact completely positive certificates.  
**Status:** Partially resolved  
**Area:** size of nonnegative symmetric factorizations  
**Last checked:** 2026-09-10  

## Context and notation

A symmetric matrix $`A`$ is **completely positive** if $`A=BB^\mathsf T`$ for an entrywise nonnegative real matrix $`B`$ with finitely many columns. Let $`\mathcal{CP}_n`$ be the cone of these matrices of order $`n`$. Its **cp-rank**, $`\mathop{\mathrm{cpr}}\nolimits(A)`$, is the minimum number of columns in such a factor, with $`\mathop{\mathrm{cpr}}\nolimits(0)=0`$. Boundaries and interiors use the usual Euclidean topology on the vector space of real symmetric matrices.

## Problem statement

Is every real completely positive matrix of order six a sum of at most nine nonnegative rank-one matrices? Equivalently, is

```math
\max_{A\in\mathcal{CP}_6}\mathop{\mathrm{cpr}}\nolimits(A)=9,
```

or, equivalently, does each $`A\in\mathcal{CP}_6`$ admit $`A=BB^\mathsf T`$ with $`B\in\mathbb R_{\ge0}^{6\times9}`$, allowing zero columns?

The lower bound nine is established. Order six is the unresolved case of the original Drew–Johnson–Loewy bound: order five satisfies it, whereas counterexamples exist in higher orders. It is included as the specific remaining case identified in the literature, rather than as one item in a dimension-by-dimension list.

A known reduction places a matrix attaining the order-six maximum on the boundary of $`\mathcal{CP}_6`$, with full ordinary rank and at least one zero entry. This reduction does not establish the nine-column bound.

## References

Abraham Berman, Mirjam Dür, and Naomi Shaked-Monderer, [*Open problems in the theory of completely positive and copositive matrices*](https://journals.uwyo.edu/index.php/ela/article/download/1477/1477), Electronic Journal of Linear Algebra **29** (2015), 46–58, §4.2, p. 53. Naomi Shaked-Monderer, [*On the DJL conjecture for order 6*, corrected arXiv v3](https://arxiv.org/html/1501.02426v3), 2017-06-01; journal version in Operators and Matrices **11** (2017), 71–88, Theorem 1.1 and Corollary 3.2.

## Status check — 2026-09-10

Rechecked [Shaked-Monderer’s corrected v3, Theorem 1.1 and Corollary 3.2](https://arxiv.org/html/1501.02426v3), and searched for later order-six DJL resolutions. The nine-term bound is proved on the boundary classes orthogonal to exceptional extremal copositive matrices, including positive nonsingular boundary matrices. Remaining maximizers can have a zero entry; this reduction is not a proof for all order-six matrices. [Behling et al. (2026), §5.6](https://doi.org/10.1007/s10957-026-02950-2), reproduces counterexamples in orders seven and twelve, not six. No full resolution was located, and the exact open-status source remains historical.

