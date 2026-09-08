# NR-03 — Full nonnegative rank of the quadratic correlation matrix

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** open; checked 2026-09-08  
**Area:** exact NMF and lower bounds for optimization formulations  
**Last checked:** 2026-09-08  

## Context and notation

All factorizations are over the real numbers. For
$X\in\mathbb R_{\ge0}^{m\times n}$, define

$$
\operatorname{rank}_+(X)=\min\{r\ge0:X=WH,\quad
W\in\mathbb R_{\ge0}^{m\times r},\ H\in\mathbb R_{\ge0}^{r\times n}\}.
$$

## Problem statement

For each integer $n\ge3$, let $C_n$ be the $2^n\times2^n$ matrix indexed by
$a,b\in\{0,1\}^n$ and defined by

$$
C_n(a,b)=(1-a^{\mathsf T}b)^2.
$$

### Question

Is $\operatorname{rank}_+(C_n)=2^n$ for every $n\ge3$?
All entries, including those for $a^{\mathsf T}b>1$, are fixed by this formula.

The matrix has ordinary rank $1+n(n+1)/2$ and is a submatrix of a slack matrix
of the correlation polytope formed from valid, possibly redundant inequalities.
The conjecture therefore asks for a large
separation between ordinary and nonnegative matrix rank with consequences for
linear programming representations.

## References

Vandaele, Gillis, Glineur, and Tuyttens,
[*Heuristics for Exact Nonnegative Matrix Factorization*](https://arxiv.org/html/1411.7245),
§6.4, Conjecture 4. Gillis,
[*Nonnegative Matrix Factorization*](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf),
§3.7, p. 96, using the name $U_n$ for this fixed matrix.

## Status evidence

Baeckelant et al.,
[*Computing Lower Bounds on the Nonnegative Rank via Non-Convex Optimization Solvers*](https://arxiv.org/html/2605.14058v2),
§6.7 and Appendix A.4, still states the full-rank conjecture. Searches for its
resolution found none. Sergeev's July 2026
[*Upper bounds for the monotone rank of the unique disjointness matrix*](https://arxiv.org/abs/2607.27014)
concerns ranks of a **partial** unique-disjointness matrix with unspecified
entries when $a^{\mathsf T}b>1$; those bounds do not determine the rank of this
prescribed completion. The open $n=3$ instance is not counted separately.
