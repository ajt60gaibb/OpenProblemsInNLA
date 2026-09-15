# MF-24 — A dimension-independent polynomial norm bound from super-identical pseudospectra

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Polynomial matrix norms and pseudospectral information  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-09-15

**Rating rationale:** Existing information controls polynomial norms with a dimension-dependent constant; a uniform comparison would strengthen pseudospectral inference about nonnormal dynamics and polynomial matrix functions.

## Resolution: negative, 15 September 2026

**Solved negatively by Georg Maierhofer (University of Cambridge).** The manuscript is dated 14 September 2026 and passed a fresh independent informal AI-agent audit on 15 September 2026. The exact dimension-dependent constants and their optimal growth remain open.

The [counterexample manuscript](../../references/mf24-counterexample/proof.pdf), **Theorem 1 and equation (15)**, constructs real nonnegative nilpotent weighted shifts of order $`N=(m+1)^2`$, for every integer $`m\ge2`$ and real $`t>1`$. All singular values agree after every complex scalar shift. For the common polynomial $`p_m(z)=\sum_{j=1}^m z^{(m+2)j}`$, it proves

```math
\frac{\|p_m(X_{m,t})\|_2}{\|p_m(Y_{m,t})\|_2}
\ge \frac{\sqrt m}{1+(m-1)/t^2},\qquad p_m(Y_{m,t})\ne0.
```

Taking $`t=m`$ gives a ratio at least $`(4/5)\sqrt m`$, so the original uniform-boundedness target is refuted. **Corollary 3** gives $`C_N\ge\sqrt{\lfloor\sqrt N\rfloor-1}`$ for $`N\ge9`$. It does not determine the sharp $`C_N`$ or close the gap to the known upper bound.

**Evidence level:** a complete written argument with reproducible exact and numerical checks, developed and self-reviewed with AI assistance. The [fresh maintainer audit](../../reviews/2026-09-15-pr264/README.md) confirms the complete negative resolution and records independent mathematical review and fresh checks. The [submitted informal Codex AI-agent audit](../../references/mf24-counterexample/independent-review.md) is also retained. No external human peer review or Lean verification is asserted. See the [source, checks and provenance](../../references/mf24-counterexample/README.md). The existing difficulty and importance ratings are retained as historical ratings of the original boundedness question.

## Context and notation

All matrices are complex and all norms are spectral norms. Write
$`s_1(M)\geq\cdots\geq s_N(M)`$ for the singular values of $`M`$. Define

```math
A\sim_{\rm sip}B\quad\Longleftrightarrow\quad
s_j(A-zI)=s_j(B-zI)\quad(z\in\mathbb C,\ 1\leq j\leq N).
```

Define the sharp comparison constant

```math
C_N=\sup\left\{
\frac{\|p(A)\|_2}{\|p(B)\|_2}:
A,B\in\mathbb C^{N\times N},\ A\sim_{\rm sip}B,
p\in\mathbb C[z],\ p(B)\ne0
\right\}.
```

As recorded in [SP-15](../../eigenvalues-and-inverse-problems/SP-15/README.md), super-identical pseudospectral data also imply ordinary similarity, so
$`p(A)=0`$ if and only if $`p(B)=0`$.

## Problem statement

Determine whether $`\sup_{N\geq1}C_N<\infty`$. Equivalently, does there exist an
absolute constant $`C`$ such that

```math
\|p(A)\|_2\leq C\|p(B)\|_2
```

for every dimension, every super-identical-pseudospectral pair and every
polynomial? Determining the sharp $`C_N`$ is the closely related quantitative
question, retained here rather than split into another entry.

## References

- Fortier Bourque and Ransford, [*Super-identical pseudospectra*](https://doi.org/10.1112/jlms/jdn085), **p. 513, immediately after Theorem 1.3**, explicitly ask both whether their $`\sqrt N`$ bound is optimal and whether a dimension-independent bound exists. The sharp-constant notation above is editorial; the boundedness question is source-stated.
- Thomas Ransford and Nathan Walsh, [*A four-mean theorem and its application to pseudospectra*, arXiv:2109.14472v2](https://arxiv.org/pdf/2109.14472v2), **9 July 2022**, **Theorem 1.3**, prove

  $`\displaystyle \|p(A)\|_2<\sqrt{N-2}\,\|p(B)\|_2\qquad(N\geq4)`$

  unless both sides vanish. **Proposition 5.1** and its following argument show sharpness for $`N=4`$: $`C_4=\sqrt2`$. **Theorem 1.4** concerns unbounded condition numbers of similarity transforms in fixed dimension, a different quantity.

Thus $`C_N\leq\sqrt{N-2}`$ for $`N\geq4`$. The small-dimensional unitary/transpose
classification gives $`C_1=C_2=C_3=1`$.

## Original scope and literature check

The following is the repository's pre-claim literature record, retained unchanged.


The unknown absolute constant, not the superseded $`\sqrt N`$ sharpness guess, is
the admission target. This comparison does not follow just from ordinary
similarity, since a badly conditioned similarity can change norms substantially.
Searches through 2026-09-11 for super-identical polynomial norm bounds,
dimension-independent bounds, sharp constants and successors to the four-mean
paper found no full solution. The current arXiv version history still ends at
v2, 9 July 2022. This is an older-source question supported by bounded searches;
no 2026 explicit open-status reaffirmation was located.
