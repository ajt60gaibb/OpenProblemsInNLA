# MF-24 — A dimension-independent polynomial norm bound from super-identical pseudospectra

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Polynomial matrix norms and pseudospectral information  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** Existing information controls polynomial norms with a dimension-dependent constant; a uniform comparison would strengthen pseudospectral inference about nonnormal dynamics and polynomial matrix functions.

## Context and notation

All matrices are complex and all norms are spectral norms. Write
$s_1(M)\geq\cdots\geq s_N(M)$ for the singular values of $M$. Define

$$
A\sim_{\rm sip}B\quad\Longleftrightarrow\quad
s_j(A-zI)=s_j(B-zI)\quad(z\in\mathbb C,\ 1\leq j\leq N).
$$

Define the sharp comparison constant

$$
C_N=\sup\left\{
\frac{\|p(A)\|_2}{\|p(B)\|_2}:
A,B\in\mathbb C^{N\times N},\ A\sim_{\rm sip}B,
p\in\mathbb C[z],\ p(B)\ne0
\right\}.
$$

As recorded in [SP-15](../../eigenvalues-and-inverse-problems/SP-15/README.md), super-identical pseudospectral data also imply ordinary similarity, so
$p(A)=0$ if and only if $p(B)=0$.

## Problem statement

Determine whether $\sup_{N\geq1}C_N<\infty$. Equivalently, does there exist an
absolute constant $C$ such that

$$
\|p(A)\|_2\leq C\|p(B)\|_2
$$

for every dimension, every super-identical-pseudospectral pair and every
polynomial? Determining the sharp $C_N$ is the closely related quantitative
question, retained here rather than split into another entry.

## References

- Fortier Bourque and Ransford, [*Super-identical pseudospectra*](https://doi.org/10.1112/jlms/jdn085), **p. 513, immediately after Theorem 1.3**, explicitly ask both whether their $\sqrt N$ bound is optimal and whether a dimension-independent bound exists. The sharp-constant notation above is editorial; the boundedness question is source-stated.
- Thomas Ransford and Nathan Walsh, [*A four-mean theorem and its application to pseudospectra*, arXiv:2109.14472v2](https://arxiv.org/pdf/2109.14472v2), **9 July 2022**, **Theorem 1.3**, prove

  $$
  \|p(A)\|_2<\sqrt{N-2}\,\|p(B)\|_2\qquad(N\geq4)
  $$

  unless both sides vanish. **Proposition 5.1** and its following argument show sharpness for $N=4$: $C_4=\sqrt2$. **Theorem 1.4** concerns unbounded condition numbers of similarity transforms in fixed dimension, a different quantity.

Thus $C_N\leq\sqrt{N-2}$ for $N\geq4$. The small-dimensional unitary/transpose
classification gives $C_1=C_2=C_3=1$.

## Scope and status check

The unknown absolute constant, not the superseded $\sqrt N$ sharpness guess, is
the admission target. This comparison does not follow just from ordinary
similarity, since a badly conditioned similarity can change norms substantially.
Searches through 2026-09-11 for super-identical polynomial norm bounds,
dimension-independent bounds, sharp constants and successors to the four-mean
paper found no full solution. The current arXiv version history still ends at
v2, 9 July 2022. This is an older-source question supported by bounded searches;
no 2026 explicit open-status reaffirmation was located.
