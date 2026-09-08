# SF-01 — Preservation of real H-matrix structure by Newton square-root iterates

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** open in the cited book; no subsequent resolution located.  
**Last checked:** 2026-09-08  

## Problem statement

For a real square matrix $Y=(y_{ij})$, define its comparison matrix by
$\mathcal M(Y)_{ii}=|y_{ii}|$ and
$\mathcal M(Y)_{ij}=-|y_{ij}|$ for $i\ne j$.
Call $Y$ a nonsingular H-matrix when
$\mathcal M(Y)=sI-B$ for some entrywise nonnegative $B$ and real
$s>\rho(B)$.

Let $n\ge1$ and let $A\in\mathbb R^{n\times n}$ be a nonsingular H-matrix
with $a_{ii}>0$ for every $i$. Consider the exact-arithmetic recurrence

$$
X_0=A,\qquad X_{k+1}=\tfrac12(X_k+X_k^{-1}A),\qquad k\ge0.
$$

Is every $X_k$ a nonsingular H-matrix with strictly positive diagonal?
The known existence of these iterates and their convergence to the principal
square root do not themselves establish the requested structure at every step.

## References and status

N. J. Higham,
[*Functions of Matrices: Theory and Computation*](https://epubs.siam.org/doi/10.1137/1.9780898717778.ch6)
(SIAM, 2008), §6.3, equation (6.12), §6.8.3, and Research Problem 6.25,
p. 170. The author's
[errata](https://nhigham.com/errata-for-functions-of-matrices-theory-and-computation/)
correct the surrounding p. 161 theorem to real H-matrices; that restriction is
adopted here. L. Lin and Z.-Y. Liu,
[*On the Square Root of an H-matrix with Positive Diagonal Elements*](https://doi.org/10.1023/A:1012931928589),
*Annals of Operations Research* 103 (2001), 339–350, concern the square root itself.
Searches on 2026-09-08 for the problem number and Newton/H-matrix
structure preservation found no resolution. The recent
[Bini–Iannazzo–Meini–Meng preprint](https://arxiv.org/html/2605.21679)
(20 May 2026), §§3–4, treats M-matrices, a narrower class. The latest explicit
open-problem evidence found for this assertion remains the 2008 book.
