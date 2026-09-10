# SP-09 — Unitary-orbit distance under finite block repetition

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-10  

**Rating rationale:** Challenging reflects preservation of a nontrivial spectral-norm orbit distance under larger unitary mixing; specialist impact concerns finite matrix amplification and operator-algebraic nearness.

## Problem statement

For $A,B\in\mathbb C^{n\times n}$, define the distance between their unitary
similarity orbits in the spectral norm by

$$
\delta_n(A,B)=\min_{U\in\mathbb C^{n\times n},\ U^*U=I_n}
\|A-U^*BU\|_2.
$$

For a positive integer $k$, write $A^{(k)}=I_k\otimes A$, the block diagonal
matrix with $k$ copies of $A$. Is it true that, for every $n\ge3$, every
finite integer $k\ge2$, and every pair of normal matrices
$A,B\in\mathbb C^{n\times n}$,

$$
\delta_{nk}\bigl(A^{(k)},B^{(k)}\bigr)=\delta_n(A,B)?
$$

Normality means $AA^*=A^*A$ and $BB^*=B^*B$. The minimizing unitary on
the left is unrestricted in dimension $nk$; it may mix different copies.
Thus the question asks whether block repetition can improve the best
unitary-similarity fit between normal matrices.

## Why it matters

This is a matrix-nearness problem with prescribed spectra. It tests whether
a structured enlargement changes the optimum in spectral norm, a metric for
which matching eigenvalues alone need not give the orbit distance.

## References

L. W. Marcoux and Y. Zhang,
[*On Specht's Theorem in UHF C*-algebras*](https://doi.org/10.1016/j.jfa.2020.108778),
Journal of Functional Analysis 280 (2021), 108778, §5, Question 5.4,
pp. 26–27; [institutional full text](https://uwspace.uwaterloo.ca/items/5359b050-4379-49b2-bdda-66ac3611d3ca).

L. W. Marcoux, P. Sarkowicz, and Y. Zhang,
[*Kaplansky's problem and unitary orbits in matrix amplifications*](https://arxiv.org/html/2508.13834v1),
arXiv:2508.13834v1 (2025), §3.5 and Propositions 3.15, 3.21, and 4.14.

## Earlier status check — 2026-09-08

Theorem 5.3 of the source proves equality for normal matrices of order two.
Theorem 5.1 establishes a strict decrease for some unrestricted matrices,
so normality cannot simply be omitted. The example after Question 5.4 uses
infinitely many copies and does not resolve the finite-$k$ question.
The direct follow-up 2508.13834v1 records the order-two result after Corollary 3.5. The corollary itself proves equality for self-adjoint matrices of every order.
Its normal-element Propositions 3.15 and 3.21 concern zero orbit distance;
its Proposition 4.14 counterexamples have no normality requirement. Neither
settles preservation of all distances for finite normal matrices.
The published §5 and these later passages were checked. Searches for `Marcoux Zhang Question
5.4 normal matrices`, `normal matrices ampliations unitary orbit distance`,
and 2025/2026 follow-ups found no finite-dimensional normal counterexample or
general proof. This is limited search evidence, not a certificate of openness.

## Audit update — 2026-09-10

Rechecked [Marcoux–Sarkowicz–Zhang](https://arxiv.org/html/2508.13834v1), Corollary 3.5: equality is proved for every pair of self-adjoint matrices, in every dimension and finite multiplicity. This substantive normal subclass was missing from the earlier status explanation. General normal matrices remain unresolved in the checked sources; finite-normal amplification searches found no completion. The nonnormal counterexamples and zero-distance results do not settle the remaining positive-distance question.
