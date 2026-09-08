# SP-08 — Rank-two maximizers of spectral spread on an entry interval

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open in general; several dimension and interval cases proved.  
**Last checked:** 2026-09-08  

## Problem statement

For an integer $n\ge2$ and $a\in[-1,1)$, let

$$
\mathcal S_n[a,1]=\{A\in\mathbb R^{n\times n}:A=A^T,\ a\le A_{ij}\le1
\text{ for all }i,j\}.
$$

The spread of $A$ is $s(A)=\lambda_{\max}(A)-\lambda_{\min}(A)$.
The Fallat–Xing conjecture asserts that there exists a matrix $B$ of rank
exactly two, every entry of which belongs to $\{a,1\}$, such that

$$
s(B)=\max_{A\in\mathcal S_n[a,1]}s(A).
$$

All diagonal entries are free to vary within the same interval as the
off-diagonal entries. The assertion concerns existence of a rank-two maximizer;
it does not assert that every maximizer has rank two. The normalization
$[a,1]$, $-1\le a<1$, is the source's reduction of the arbitrary nondegenerate
real-interval problem. All dimensions and intervals form one problem.

## Why it matters

The conjecture reduces an eigenvalue optimization over a full symmetric
matrix family to a low-rank extremizer. It sharpens spectral bounds obtainable
from entrywise uncertainty alone.

## References

S. M. Fallat and Y. Xing, [*On the spread of certain normal matrices*](https://doi.org/10.1080/03081087.2012.703189), Linear
and Multilinear Algebra 60 (2012), 1391–1407, §2. N. J. Calkin, R. M. Corless,
L. Gonzalez-Vega, J. R. Sendra, and J. Sendra,
[*On the maximal spread of symmetric Bohemian matrices*](https://arxiv.org/abs/2510.15919),
2025, §1 (displayed Fallat–Xing conjecture), §§3.2, 7–8, and §10.

## Status check

Version 1 of the 2025 paper is the latest listed version checked. It proves
the conjecture for all $a\in(-1,1)$ when $2\le n\le7$, and for $a=0$
when $2\le n\le8$ or $3$ divides $n$. The case $a=-1$ was already proved
by Zhan. Its conclusion explicitly records a gap in the authors' attempted
general proof. The [authors' supporting repository](https://github.com/rcorless/BohemianSpread)
confirms the finite computational ranges. Searches for `Fallat Xing spread
conjecture proof 2026` and later maximal-spread papers found no general
resolution. Restricting entries to interval endpoints alone is already known
and is not counted separately.
