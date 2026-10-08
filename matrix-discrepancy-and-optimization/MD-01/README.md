# MD-01 — The sharp Lovász-theta constant for dense random graphs

**Difficulty:** challenging  
**Importance:** broadly interesting  
**Status:** Solution claimed  
**Last checked:** 2026-10-08

**Rating rationale:** A sharp expectation constant requires new random SDP analysis beyond order bounds; it connects matrix optimization with probabilistic combinatorics.

The difficulty and importance ratings above are historical ratings of the
original open target.

## Full-resolution claim — checked 6 October 2026

Aaron Potechin and Jeff Xu, [*Sharp Lovász-Theta Bounds on Random
Graphs*](https://arxiv.org/abs/2609.30064v1), arXiv:2609.30064v1, first
submitted 24 September 2026. In §1.1, **Theorem 1.2 and Corollary 1.3**
(printed p. 3 of the [full manuscript](https://arxiv.org/pdf/2609.30064)),
the authors claim that $`\vartheta(G_n)/\sqrt n\to1`$ in probability.
Appendix F (printed pp. 76–77) identifies their formulation with the
trace-normalized SDP used in this entry.
The [official FOCS 2026 accepted-paper list](https://focs.computer.org/2026/accepted-papers/)
includes this paper; acceptance is recorded separately from publication in
the proceedings.

**Correspondence with the expectation target.** The claimed probabilistic
limit implies the original expectation limit by the following elementary
uniform-integrability argument. Let $`A_n`$ be the ordinary zero-one
adjacency matrix and put $`B_n=J-I-2A_n`$. For every matrix $`X`$ feasible
in the original SDP, the edge constraints give

```math
\langle J,X\rangle=\langle I+B_n,X\rangle
\le1+\|B_n\|_2,
\qquad
0\le\frac{\vartheta(G_n)}{\sqrt n}
\le\frac{1+\|B_n\|_2}{\sqrt n}.
```

The independent upper-triangular entries of $`B_n`$ are uniform signs.
For a fixed real unit vector $`x`$, the sum
$`x^TB_nx=2\sum_{i< j}(B_n)_{ij}x_ix_j`$ has squared coefficient sum at
most two. The elementary exponential-moment bound for a sum of independent
signs therefore gives $`\Pr\{|x^TB_nx|>t\}\le2e^{-t^2/4}`$.
A $`1/4`$-net of the real unit sphere with at most $`9^n`$ points controls
the norm of a symmetric matrix within a factor of two. Consequently,

```math
\Pr\{\|B_n\|_2>s\}
\le\min\{1,2\cdot9^n e^{-s^2/16}\},
\qquad
\mathbb E\|B_n\|_2^2
\le16(n\log9+\log2+1).
```

The moment bound follows by integrating this tail bound. Thus
$`\sup_n\mathbb E[(\vartheta(G_n)/\sqrt n)^2]<\infty`$, so the
normalized Lovász numbers are uniformly integrable. Theorem 1.2's
high-probability upper bound therefore gives
$`\limsup_n\mathbb E\vartheta(G_n)/\sqrt n\le1`$.
For the lower bound, the deterministic inequality
$`\vartheta(G)\vartheta(\bar G)\ge n`$ and the fact that
$`G_n`$ and $`\bar G_n`$ have the same distribution give, by the
arithmetic-geometric mean inequality,
$`\mathbb E\vartheta(G_n)\ge\sqrt n`$ for every $`n`$.
Together these establish the original expectation limit, conditional on
Theorem 1.2. The argument preserves the original SDP, graph ensemble and
quantifiers; it does not replace the expectation statement with a
probabilistic one.

**Evidence level, 8 October 2026:** an [independent AI-agent review](../../reviews/2026-10-08-claimed-solutions/MD-01.md)
checked the theorem's match to the expectation target, the bridge above,
and the witness construction through its main dependency chain. It could
not independently certify the decisive graph-matrix norm, product and
correction estimates (Theorem 3.27/Corollary 3.28 and Theorems 4.7 and 4.17).
The status therefore remains **Solution claimed**; no Lean verification or
external human peer review is asserted. The original mathematical statement
follows unchanged.

## Original problem statement

Let $`G_n`$ be the simple random graph on $`n`$ labelled vertices in which each unordered pair is an edge independently with probability $`1/2`$. For a graph $`G`$, define its Lovász number by

```math
\vartheta(G)=\max\{\langle J,X\rangle:X\in\mathbb R^{n\times n},\ X=X^T\succeq0,\ \mathop{\mathrm{tr}}\nolimits X=1,\ X_{ij}=0\text{ for }\{i,j\}\in E(G)\},
```

where $`J`$ is the all-ones matrix and $`\langle J,X\rangle=\sum_{i,j}X_{ij}`$.

**Conjecture.** $`\displaystyle\lim_{n\to\infty}\mathbb E\vartheta(G_n)/\sqrt n=1`$.

This asks for the leading constant of a random semidefinite matrix optimization problem. It is an expectation statement; convergence in probability is not substituted for it.

## References

1. A. S. Bandeira, D. Dmitriev, K. Lucca, P. Nizić-Nikolac, and A. Rödder, *Randomstrasse101: Open Problems of 2025*, Entry 9, Conjecture 17 and the preceding SDP definition. [Archived paper](https://arxiv.org/abs/2603.29571).
2. A. Potechin and J. Xu, [*Sharp Lovász-Theta Bounds on Random Graphs*](https://arxiv.org/abs/2609.30064v1), arXiv:2609.30064v1, 24 September 2026, §1.1, Theorem 1.2 and Corollary 1.3, printed p. 3; accepted for FOCS 2026.

## Status check — 2026-09-10

The archived 2026 paper retains the conjecture. Targeted searches for the Lovász number of dense Erdős–Rényi graphs and a sharp leading constant through September 2026 found no resolution. The adjacent circulant problem uses a different random matrix ensemble and is recorded separately.

**Audit update (2026-09-10):** Rechecked the 2026 Conjecture 17 and searched for a sharp dense-random-graph theta constant. No resolution of the expectation limit was located. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
