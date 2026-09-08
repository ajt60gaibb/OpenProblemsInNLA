# MF-17 — Optimal uniform growth after inversion of an exponentially stable generator

**Difficulty:** hard  
**Importance:** interesting to the community  
**Provenance:** explicit fixed-bound formalization of the source's growth question.  
**Last checked:** 2026-09-08

**Status:** no sharp growth order found in screening on 2026-09-08.  

For each fixed real number $M>1$, let $\mathcal A_M$ consist of all pairs $(H,A)$ such that $H$ is a complex Hilbert space and $A$ is the generator of a strongly continuous semigroup $T(s)$ on $H$ satisfying
$$
\|T(s)\|_{\mathcal L(H)}\leq M e^{-s}
\qquad(s\geq0).
$$
Here $A$ may be unbounded and is understood on its dense domain. Exponential stability implies that $0$ belongs to the resolvent set of $A$, so $A^{-1}$ is bounded on $H$ and its exponential is defined by the operator-norm convergent power series.

Determine, for each fixed $M>1$, the asymptotic order as $t\to\infty$ of
$$
G_M(t)=
\sup_{(H,A)\in\mathcal A_M}
\|\exp(tA^{-1})\|_{\mathcal L(H)}.
$$
An asymptotic order means a rate $g_M(t)$ with matching positive upper and lower multiplicative bounds for all sufficiently large $t$; their constants may depend on $M$, but must be uniform over $(H,A)\in\mathcal A_M$.

The source's Problem 1.3 asks for the optimal inverse-semigroup growth for exponentially stable Hilbert-space semigroups. The envelope above makes the dependence on the original semigroup bound explicit. This formalization is supported by uniform upper estimates and examples in the same normalized class, rather than attributed verbatim to the source. The problem concerns operator stability and rational time-stepping analysis, extending finite-dimensional matrix exponential questions.

## References

1. E. Lorist, M. Meyries, and M. Veraar, *A solution to the inverse generator problem and related questions*, arXiv:2608.06272v3 (2026), Problem 1.3, Theorem 1.2(2), and Section 1.3 on numerical stability. [Paper](https://arxiv.org/html/2608.06272v3).
2. C. J. K. Batty, A. Gomilko, and Y. Tomilov, *A Besov algebra calculus for generators of operator semigroups and related norm-estimates*, Mathematische Annalen 379 (2021), pp. 23–93, Corollary 5.7: explicit constants depending only on the semigroup bound and decay rate. Their generator notation is $-A$. [Published paper](https://link.springer.com/article/10.1007/s00208-019-01924-2).
3. H. Zwart, *Growth Estimates for $\exp(A^{-1}t)$ on a Hilbert Space*, Semigroup Forum 74 (2007), pp. 487–494, Theorem 2.2 and Corollary 2.3: the logarithmic upper bound. [Published paper](https://link.springer.com/article/10.1007/s00233-006-0679-1).

## Status check — 2026-09-08

checked the current arXiv history, with latest version v3 dated 2026-08-26 and no withdrawal, and searched “inverse generator Problem 1.3” and “inverse generator growth 2026 logarithmic”. Corollary 5.7 of reference 2 gives, in the present sign convention and at decay rate one,
$$
G_M(t)\leq2M^2\bigl(2-e^{-1}+e^{-1}\log t\bigr),
\qquad t>1.
$$
Theorem 1.2(2) of reference 1 gives examples with a doubly logarithmic lower bound raised to a positive exponent, while the original semigroup bound is $1+C\alpha/(1-\alpha)$ for an absolute $C$ and $0<\alpha<1$. Thus its parameters allow examples within each fixed $M>1$ class. These estimates do not determine the matching asymptotic order. The older yes/no inverse-generator problem was resolved negatively in the 2026 paper and is not listed as open here.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
