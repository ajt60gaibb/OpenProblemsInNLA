# IV-01 — Two-vertex certification of nonsingular sign regularity

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** open; checked 2026-09-08  
**Area:** structured matrices and interval linear algebra  
**Last checked:** 2026-09-08  

## Problem statement

For $\epsilon\in\{-1,1\}^n$, call a real $n\times n$ matrix $M$
**nonsingular sign regular with signature $\epsilon$** if $\det M\ne0$ and
every minor of order $k$ has determinant $d$ satisfying $\epsilon_k d\ge0$,
for every $1\le k\le n$.

Let $n\ge5$ and let $L,U\in\mathbb R^{n\times n}$ satisfy $L\le U$
entrywise. Define the two checkerboard vertex matrices

$$
A^-_{ij}=\begin{cases}L_{ij},&i+j\text{ even},\\U_{ij},&i+j\text{ odd},\end{cases}
\qquad
A^+_{ij}=\begin{cases}U_{ij},&i+j\text{ even},\\L_{ij},&i+j\text{ odd}.\end{cases}
$$

### Question

If $A^-$ and $A^+$ are nonsingular sign regular with the same
signature $\epsilon$, must every real matrix $M$ with $L\le M\le U$ be
nonsingular sign regular with signature $\epsilon$?

The implication would certify a property of an entire interval of matrices
from only two of its vertices. Allowing zero minors is essential to the
remaining problem.

## References

Jürgen Garloff, Mohammad Adm, and Jihad Titi,
[*A Survey of Classes of Matrices Possessing the Interval Property and Related Properties*](https://www.reliable-computing.org/reliable-computing-22-pp-001-014.pdf),
Reliable Computing **22** (2016), 1–14, Conjecture 3.1, p. 7. Adm and Garloff,
[*Certification of the Sign Regularity of Matrix Intervals*](https://doi.org/10.1007/s44146-026-00223-y),
Acta Scientiarum Mathematicarum, published January 17, 2026, §3, especially
the question following Theorem 3.2 and the discussion of admissible signatures.

## Status evidence

The 2026 survey explicitly retains this question. It
records positive results for strictly sign regular matrices, totally
nonnegative matrices, tridiagonal matrices, and certain signatures covering
all orders at most four. Theorem 3.3 also covers intervals whose fixed entries
$L_{ij}=U_{ij}$, if any, all have the same parity of $i+j$; fixed entries of
both parities are allowed in the general question. It also records
counterexamples when nonsingularity is omitted. Searches for sign-regular interval conjectures and subsequent
2026 results found no resolution of the displayed implication.
