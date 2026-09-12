# NR-02 — Additivity for Cartesian-product slack matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because additivity across arbitrary polytopes is a general structural barrier for extension complexity; community importance links optimal factorizations with compositional linear optimization models.  
**Status:** Partially resolved  
**Area:** nonnegative rank and polyhedral optimization  
**Last checked:** 2026-09-10  

## Context and notation

All factorizations are over the real numbers. For
$`X\in\mathbb R_{\ge0}^{m\times n}`$, define

```math
\mathop{\mathrm{rank}}\nolimits_+(X)=\min\{r\ge0:X=WH,\quad
W\in\mathbb R_{\ge0}^{m\times r},\ H\in\mathbb R_{\ge0}^{r\times n}\}.
```

## Problem statement

Let $`P\subset\mathbb R^d`$ and $`Q\subset\mathbb R^e`$ be full-dimensional
polytopes with $`d,e\ge1`$. Let $`S\in\mathbb R_{\ge0}^{m\times n}`$ and
$`T\in\mathbb R_{\ge0}^{p\times q}`$ be their slack matrices: rows correspond
to all facets in irredundant inequality descriptions, columns to all vertices,
and each entry is the right-hand side minus the left-hand side of that facet
inequality at that vertex. Construct $`C\in\mathbb R_{\ge0}^{(m+p)\times nq}`$
by giving it one column for each pair $`(i,j)`$ of vertices:

```math
C[:,(i,j)]=\begin{pmatrix}S[:,i]\\T[:,j]\end{pmatrix}.
```

### Question

Is

```math
\mathop{\mathrm{rank}}\nolimits_+(C)=\mathop{\mathrm{rank}}\nolimits_+(S)+\mathop{\mathrm{rank}}\nolimits_+(T)
```

always true? The hypotheses that $`S,T`$ are polytope slack matrices are part of
the question. Through the slack-factorization theorem, this also asks whether
the minimum number of inequalities in an extended formulation is additive
under Cartesian products.

## References

Gillis, [*Nonnegative Matrix Factorization*](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf),
§3.6.5, pp. 93–94. Hans Raj Tiwary, Stefan Weltge, and Rico Zenklusen,
[*Extension complexities of Cartesian products involving a pyramid*](https://arxiv.org/abs/1702.01959),
Information Processing Letters **128** (2017), 11–13, introduction and main
theorem.

## Status check — 2026-09-10

Rechecked [Tiwary–Weltge–Zenklusen](https://arxiv.org/abs/1702.01959) and [Weltge’s 2022 workshop question](https://www.cargese.org/2022/open-problems.pdf), then searched for later product-additivity proofs and counterexamples. Equality is proved whenever one factor is a pyramid, a substantive portion of the displayed target. The unrestricted equality remains open in the latest explicit source located; no subsequent full resolution was found. The 2022 date limits the strength of the current-status evidence.

