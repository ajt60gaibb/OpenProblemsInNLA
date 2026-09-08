# Matrix properties under interval uncertainty

This chapter contains **2 admitted problems**. Ratings are editorial; status
checks were performed on **2026-09-08**. The questions concern exact properties
of sets of matrices with independently uncertain entries, as used in verified
numerical computation.

<a id="iv-01"></a>

## IV-01 — Two-vertex certification of nonsingular sign regularity

- **Difficulty:** challenging
- **Importance:** interesting to specialist
- **Status:** open; checked 2026-09-08
- **Area:** structured matrices and interval linear algebra

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

**Problem.** If $A^-$ and $A^+$ are nonsingular sign regular with the same
signature $\epsilon$, must every real matrix $M$ with $L\le M\le U$ be
nonsingular sign regular with signature $\epsilon$?

The implication would certify a property of an entire interval of matrices
from only two of its vertices. Allowing zero minors is essential to the
remaining problem.

**References.** Jürgen Garloff, Mohammad Adm, and Jihad Titi,
[*A Survey of Classes of Matrices Possessing the Interval Property and Related Properties*](https://www.reliable-computing.org/reliable-computing-22-pp-001-014.pdf),
Reliable Computing **22** (2016), 1–14, Conjecture 3.1, p. 7. Adm and Garloff,
[*Certification of the Sign Regularity of Matrix Intervals*](https://doi.org/10.1007/s44146-026-00223-y),
Acta Scientiarum Mathematicarum, published January 17, 2026, §3, especially
the question following Theorem 3.2 and the discussion of admissible signatures.

**Status evidence.** The 2026 survey explicitly retains this question. It
records positive results for strictly sign regular matrices, totally
nonnegative matrices, tridiagonal matrices, and certain signatures covering
all orders at most four. Theorem 3.3 also covers intervals whose fixed entries
$L_{ij}=U_{ij}$, if any, all have the same parity of $i+j$; fixed entries of
both parities are allowed in the general question. It also records
counterexamples when nonsingularity is omitted. Searches for sign-regular interval conjectures and subsequent
2026 results found no resolution of the displayed implication.

<a id="iv-02"></a>

## IV-02 — Exact determinant ranges of general tridiagonal interval matrices

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** interval linear algebra; determinants; computational complexity

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

**References:** Horáček, Hladík, and Matějka,
[*Determinants of interval matrices*](https://doi.org/10.13001/1081-3810.3719),
Electronic Journal of Linear Algebra 33 (2018), 99–112,
**§5.4, p. 106**, immediately after Proposition 5.6;
[journal PDF](https://journals.uwyo.edu/index.php/ela/article/download/1831/1831/1831).
The corresponding location in [arXiv:1809.03736v1](https://arxiv.org/abs/1809.03736v1)
is §6.4, p. 9, after Proposition 6.7. The source proves polynomial
computability for interval tridiagonal H-matrices and explicitly leaves
general tridiagonal interval matrices open.

**Status check (2026-09-08):** Searches for `tridiagonal interval determinant
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
