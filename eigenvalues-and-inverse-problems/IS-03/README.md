# IS-03 — Johnson's derivative-realizability conjecture

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open.  
**Last checked:** 2026-09-08  

## Problem statement

For every integer $n\geq5$ and every real entrywise-nonnegative matrix
$A\in\mathbb R^{n\times n}$, define $p_A(z)=\det(zI-A)$.
Must there exist an entrywise-nonnegative
$B\in\mathbb R^{(n-1)\times(n-1)}$ such that

$$
\det(zI-B)=\frac1n p_A'(z)\qquad\text{as polynomials in }z?
$$

Equivalently, the critical points of the characteristic polynomial, counted
with multiplicity, would themselves form a realizable spectrum of the smaller
order. Neither $A$ nor $B$ is assumed symmetric or diagonalizable. The
realization must have exactly order $n-1$; allowing arbitrary additional zero
eigenvalues changes the problem. This would provide a dimension-reduction
operation for nonnegative spectral realization.

## References

Hoover, McCormick, Paparella, and Thrall,
[*On the realizability of the critical points of a realizable list*](https://arxiv.org/pdf/1712.05454),
Conjecture 1.2, p. 2, and §6. The paper credits the conjecture to Johnson and
records the Cronin–Laffey low-order results.

## Status check

Searches for `Johnson conjecture derivative nonnegative
matrix characteristic polynomial proof counterexample`, `1712.05454 2026`,
and `Monov conjecture solved` found no general resolution. The source proves
several classes and records the solved cases $n\leq4$, and
$n\leq6$ with $\operatorname{tr}A=0$. Nonnegative power sums alone are a
different hypothesis. Monov's weaker moment conjecture is not separately
counted here.
