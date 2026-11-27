# NR-02 — Additivity for Cartesian-product slack matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Historical rating of the original target. Additivity across arbitrary polytopes posed a general structural barrier for extension complexity, linking optimal factorizations with compositional linear optimization models.  
**Status:** Solved  
**Area:** nonnegative rank and polyhedral optimization  
**Last checked:** 2026-11-27

## Negative resolution — 27 November 2026

Minhao Liu's [Theorem 1](https://arxiv.org/html/2611.33631v1#S1), submitted
25 November 2026, constructs a full-dimensional rational polytope
$`P\subset\mathbb R^{24}`$ with 50 facets and 150 vertices. The extension
complexities are 40 for $`P`$ and 79 for $`P\times P`$. If $`S`$ is the full
facet–vertex slack matrix of $`P`$ and $`C`$ is the matrix in the original
statement with $`Q=P`$, Yannakakis' factorization theorem gives

```math
\mathop{\mathrm{rank}}\nolimits_+(C)=79
<80=2\mathop{\mathrm{rank}}\nolimits_+(S).
```

[Section 5.3](https://arxiv.org/html/2611.33631v1#S5.SS3) supplies the
polytope inequalities. Proposition 9 gives the two real nonnegative ranks
for the selected rows, and Theorem 3 transfers them to the full slack
matrices by adding 26 for one factor and 52 for the square.

The [independent Codex proof note](solution.md) verifies the strict gap
with a limiting argument for Liu's matrices and a direct proof that the
retained coordinate rows are facets. The review is informal and
AI-assisted. Lluis Eriksson's
[companion verification](https://airr.science/papers/ARR-2026-0WKHQBJJDA8C4VPT/versions/v1/)
checks selected finite steps using exact arithmetic and Lean.

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

## Reviewed continuation — 13 September 2026

Sidney Holden (Center for Computational Biology, Flatiron Institute, Simons Foundation) supplies a computer-assisted proof that $`\mathop{\mathrm{xc}}\nolimits(P\times Q)=12`$ whenever both factors are polygons of extension complexity six. The [fourth-round report](../../references/holden-continuations-2026-09-13/NR-02/report.pdf), main theorem and geometry-to-Boolean reduction, reduces this statement to ten exact LRAT refutations. The broader inherited all-polytopes corollary in the package was not independently re-audited in this submission.

This was the basis for the September **Partially resolved** classification.
The [independent informal Codex AI-agent review](../../references/holden-continuations-2026-09-13/verification/NR-02/review.md) records its accepted scope and checks. [Submission, original package, reproduction and verified affiliation](../../references/holden-continuations-2026-09-13/README.md). This is not external human peer review or formal verification; no Lean verification was performed.

