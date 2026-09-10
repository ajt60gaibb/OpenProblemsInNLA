# TR-23 — Irreducibility of asymptotic tensor-rank sublevel varieties

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to specialist  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** Controlling irreducibility for every tensor-power cost sublevel is a foundational geometric question stronger than finiteness of the attainable costs. Its immediate audience is specialists in the algebraic geometry of tensor complexity.

## Problem statement

Let $\mathbb F$ be an algebraically closed field, let $k\geq3$, and let $d_1,\ldots,d_k$ be positive integers. Write
$V=\mathbb F^{d_1}\otimes\cdots\otimes\mathbb F^{d_k}$.
For $T\in V$, let $R(T)$ be its tensor rank, and define its asymptotic rank by
$$
\widetilde R(T)=\lim_{m\to\infty}R(T^{\boxtimes m})^{1/m},
$$
where $\boxtimes$ groups corresponding modes of tensor powers; put $\widetilde R(0)=0$.

For every real $a\geq0$, is the set
$$
V_{\leq a}=\{T\in V:\widetilde R(T)\leq a\}
$$
an irreducible algebraic variety?

The source proves that these sets are Zariski closed. The open assertion is that none can be written as the union of two proper Zariski-closed subsets. All fields, formats, and thresholds above are quantified; $0\in V_{\leq a}$ avoids the empty-set convention for irreducibility.

## Why it matters

For matrices, bounded rank defines an irreducible determinantal variety. The question asks whether a comparable geometric unity survives when tensor rank is replaced by its asymptotic computational cost. A positive answer would constrain the number of costs possible in a format and the ways low-cost tensor families can degenerate.

This is stronger than merely asking for a finite set of asymptotic-rank values. The source lists the two questions separately and records the implication from irreducibility to discreteness; no converse is claimed.

## References and status check

1. M. Christandl, K. Hoeberechts, H. Nieuwboer, P. Vrana, and J. Zuiddam, *Asymptotic tensor rank is characterized by polynomials*, [arXiv:2411.15789v2](https://arxiv.org/pdf/2411.15789v2), Theorem 1.2 and §5 second bullet, p.17.
2. Their [STOC 2025 publication](https://ir.cwi.nl/pub/36100/36100.pdf), p.753, “Geometric properties; irreducibility.”
3. J. Zuiddam, [November 2025 research slides](https://staff.fnwi.uva.nl/j.zuiddam/talks/simons-14nov-2025.pdf), “Open problems,” question (2).

### Status check — 2026-09-10

Checked the June 2026 arXiv revision, §5 second bullet, and the STOC 2025 irreducibility discussion, with targeted 2025–2026 searches. The sources leave irreducibility open for tensors of order at least three. Closedness is proved, but neither it nor the excluded matrix case supplies a nontrivial resolved part of this universal irreducibility target. Conditional implications from the full asymptotic-rank conjecture are not unconditional solutions. No general proof or counterexample was located.
