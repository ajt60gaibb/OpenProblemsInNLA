# NM-01 — Polynomial-time minimum-volume decision under sufficient scattering

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Topic:** structured matrix factorization; global optimization  
**Last checked:** 2026-09-08  
**Status:** open; admitted after a bounded literature search found no resolution.  

## Context and notation

For $H\in\mathbb R_+^{r\times n}$, let
$\operatorname{cone}(H)=\{Hy:y\in\mathbb R_+^n\}$ and let $e_d$ be the
all-ones vector in $\mathbb R^d$. Here **SSC** means
the precise version in Gillis's Definition 4.15:

$$
\mathcal C_r=\{x\in\mathbb R_+^r:
e_r^Tx\geq\sqrt{r-1}\|x\|_2\}\subseteq\operatorname{cone}(H),
$$

and every orthogonal $Q\in\mathbb R^{r\times r}$ satisfying
$\operatorname{cone}(H)\subseteq\operatorname{cone}(Q)$ is a permutation
matrix. Some later sources use a stronger second condition involving the
boundary of the dual cone; that condition is not substituted here.

For $X\in\mathbb R^{m\times n}$ and $r=\operatorname{rank}(X)$, the
minimum-volume problem considered here is

$$
\min_{W\in\mathbb R^{m\times r},\ H\in\mathbb R_+^{r\times n}}
\det(W^TW)
\quad\text{subject to}\quad
X=WH,\qquad e_r^TH=e_n^T.\tag{MV}
$$

In particular, $W$ is unrestricted in sign and the **columns** of $H$ sum
to one. This is min-vol NMF (1), Definition 4.42 of the book.

## Problem statement

Consider the following rational-input decision version of minimum-volume
optimization. The input is $X\in\mathbb Q^{m\times n}$, an integer
$2\leq r\leq\min(m,n)$, and $\tau\in\mathbb Q_{\geq0}$, with the promise
that $\operatorname{rank}(X)=r$ and that there exist real factors
$X=W_\star H_\star$ feasible for (MV) with $H_\star$ satisfying SSC.
These factors are not supplied. Decide whether

$$
\exists W\in\mathbb R^{m\times r},\ H\in\mathbb R_+^{r\times n}:
\quad X=WH,\quad e_r^TH=e_n^T,\quad\det(W^TW)\leq\tau.
$$

Does a polynomial-time algorithm exist, with time measured in the total
binary input length? Randomization is allowed with success probability at
least $2/3$ on every promised input. The algorithm must run in polynomial
time on all inputs but need only answer correctly on promised inputs.
Checking the SSC promise is not part of the task. This decision formulation
fixes the computational model of the book's polynomial-solvability
conjecture; it does not assert an equivalence with exact factor recovery.

## References

Gillis, [*Nonnegative Matrix Factorization*](https://doi.org/10.1137/1.9781611976410),
§4.3.3.6, pp. 148–149, with Definitions 4.15 and 4.42 and Theorem 4.43;
[author-hosted book](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf).
Barbarino, Gillis, and Saha,
[*Robustness of Minimum-Volume Nonnegative Matrix Factorization under an Expanded Sufficiently Scattered Condition*](https://arxiv.org/html/2511.04291v1),
§5, final research question.

## Status check

Searches for `minimum-volume NMF polynomial time
sufficiently scattered` and `minimum volume simplex sufficiently scattered
algorithm 2026 2025` found no polynomial-time guarantee for this promise.
The November 2025 paper still asks for complexity results under its stronger
$p$-SSC assumption. Its robustness theorems assume a globally optimal
minimum-volume solution; they do not compute one in polynomial time.
The book explains why the maximum-inscribed-ellipsoid approach can require
exponentially many polytope facets.
