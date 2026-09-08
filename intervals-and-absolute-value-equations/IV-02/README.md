# IV-02 — Exact determinant ranges of general tridiagonal interval matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** interval linear algebra; determinants; computational complexity  
**Last checked:** 2026-09-08  
**Status:** open; admitted after a bounded literature search found no resolution.  

## Problem statement

For $n\geq2$, let the input consist of $3n-2$ closed real intervals with
rational endpoints: diagonal intervals $[\underline a_i,\overline a_i]$
for $1\leq i\leq n$, upper-diagonal intervals
$[\underline b_i,\overline b_i]$, and lower-diagonal intervals
$[\underline c_i,\overline c_i]$ for $1\leq i<n$.
All lower endpoints are at most their upper endpoints. Define

$$
\mathcal T=\{T\in\mathbb R^{n\times n}:
T_{ii}\in[\underline a_i,\overline a_i],\quad
T_{i,i+1}\in[\underline b_i,\overline b_i],\quad
T_{i+1,i}\in[\underline c_i,\overline c_i],\quad
T_{ij}=0\text{ if }|i-j|>1\}.
$$

All uncertain entries vary independently. Does a deterministic algorithm
exist that returns the two exact rational numbers

$$
d_- = \min_{T\in\mathcal T}\det T,
\qquad
d_+ = \max_{T\in\mathcal T}\det T
$$

in time polynomial in the total binary input length? The target is the
exact range $[d_-,d_+]$, including instances containing singular matrices
and intervals crossing zero. Rational output is appropriate because the
determinant is affine in each entry separately and its extrema are attained
at endpoint matrices. The polynomial bound must be uniform in $n$.

## References

Horáček, Hladík, and Matějka,
[*Determinants of interval matrices*](https://doi.org/10.13001/1081-3810.3719),
Electronic Journal of Linear Algebra 33 (2018), 99–112,
**§5.4, p. 106**, immediately after Proposition 5.6;
[journal PDF](https://journals.uwyo.edu/index.php/ela/article/download/1831/1831/1831).
The corresponding location in [arXiv:1809.03736v1](https://arxiv.org/abs/1809.03736v1)
is §6.4, p. 9, after Proposition 6.7. The source proves polynomial
computability for interval tridiagonal H-matrices and explicitly leaves
general tridiagonal interval matrices open.

## Status check (2026-09-08)

Searches for `tridiagonal interval determinant
complexity`, `tridiagonal determinant range`, and `tridiagonal interval
determinant polynomial 2026` found no resolution for independent-entry
exact ranges. Two superficially conflicting Thirupathi–Thamaraiselvan papers,
[*Symbolic Algorithm for Inverting General k-Tridiagonal Interval Matrices*](https://doi.org/10.28924/2291-8639-21-2023-20)
and [*A Symbolic Algorithm for Solving Doubly Bordered k-Tridiagonal Interval Linear Systems*](https://doi.org/10.28924/2291-8639-21-2023-87),
both published in 2023, use different generalized arithmetic (§2.2,
pp. 3–4). Their multiplication centers the result at the product of
midpoints and takes the smaller distance to the standard product endpoints.
Consequently it sends $[1,2]$ and $[2,3]$ to $[2,11/2]$, while independent
products range over $[2,6]$. Their symbolic determinant algorithms therefore
do not establish exact ranges in the sense defined above.
