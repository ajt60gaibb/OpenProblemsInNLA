# MF-23 — Complete Crouzeix conjecture

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Matrix-valued polynomial functional calculus  
**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** The uniform bound must survive arbitrary matrix amplification, beyond the scalar functional calculus; it would give sharp bounds for block matrix functions and connect numerical-range estimates to dilation and similarity theory.

## Context and notation

All matrices are complex, and all norms are Euclidean operator norms. For
$A\in\mathbb C^{n\times n}$ define

$$
W(A)=\{x^*Ax:x\in\mathbb C^n,\ x^*x=1\}.
$$

If $F(z)=[f_{ij}(z)]_{i,j=1}^m$ has polynomial entries, let
$F(A)=[f_{ij}(A)]_{i,j=1}^m$, an $mn\times mn$ block matrix.

## Problem statement

Prove or disprove that, for every $n,m\geq1$, every
$A\in\mathbb C^{n\times n}$ and every matrix polynomial
$F\in\mathbb C^{m\times m}[z]$,

$$
\|F(A)\|_2\leq 2\max_{z\in W(A)}\|F(z)\|_2.
$$

This is the complete, rather than scalar, numerical-range spectral-set question.
It controls simultaneous polynomial functions and hence block approximation
errors with one constant independent of matrix and block sizes.

## References

- Michel Crouzeix, [*Numerical range and functional calculus in Hilbert space*](https://doi.org/10.1016/j.jfa.2006.10.013), *Journal of Functional Analysis* **244**(2), 668–690 (2007). Original source for the complete conjecture, as explicitly attributed in the next source.
- Per Åhag, Rafał Czyż and Jani Virtanen, [*Square Functions, Complete Crouzeix Conjecture in Dimension Three, and the Clouâtre–Ostermann–Ransford conjecture*, arXiv:2608.27346v3](https://arxiv.org/html/2608.27346v3), **9 September 2026**, Introduction, equation **(1.2)** and **Theorem 1.1**. This current version states the exact target and explicitly distinguishes it from the scalar proofs. It claims the complete bound for $n\leq3$. Its counterexample reduction leaves only $2\times2$ matrix polynomials to check when $n=4$.
- Michel Crouzeix and César Palencia, [*The numerical range is a $(1+\sqrt2)$-spectral set*](https://doi.org/10.1137/17M1116672), *SIAM Journal on Matrix Analysis and Applications* **38**(2), 649–655 (2017). The complete universal upper bound is $1+\sqrt2$.

## Scope and status check

The target is source-stated, not an editorial extension of the scalar conjecture.
The August 2026 scalar proof claims by Jin and by Lorist–Schwenninger do not settle
it: the September 9 primary manuscript explicitly addresses this distinction.
The $n=3$ result is a recent preprint claim; the full displayed target remains
unresolved even if that claim is accepted. Searches through the check date for
complete Crouzeix proofs, matrix-valued Crouzeix inequalities and later versions
found no full solution. The version was inspected as both HTML and PDF; the
inequality is on PDF page 2, immediately before Theorem 1.1.
