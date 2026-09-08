# NR-04 — The nonnegative rank of the nine-point distance matrix

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** hard  
**Importance:** interesting to specialist  
**Status:** open; checked 2026-09-08  
**Area:** exact factorization of Euclidean distance matrices  
**Last checked:** 2026-09-08  

## Context and notation

All factorizations are over the real numbers. For
$X\in\mathbb R_{\ge0}^{m\times n}$, define

$$
\operatorname{rank}_+(X)=\min\{r\ge0:X=WH,\quad
W\in\mathbb R_{\ge0}^{m\times r},\ H\in\mathbb R_{\ge0}^{r\times n}\}.
$$

## Problem statement

Let $D\in\mathbb R_{\ge0}^{9\times9}$ have entries
$D_{ij}=(i-j)^2$ for $1\le i,j\le9$.

### Question

Does there exist an exact factorization
$D=WH$ with $W\in\mathbb R_{\ge0}^{9\times6}$ and
$H\in\mathbb R_{\ge0}^{6\times9}$? Equivalently, is
$\operatorname{rank}_+(D)=6$ or $7$?

## References

Baeckelant, Vandaele, and Gillis,
[*Computing Lower Bounds on the Nonnegative Rank via Non-Convex Optimization Solvers*](https://arxiv.org/html/2605.14058v2),
Appendix A.1, Table 6 and its final paragraph, expressly isolates this case.
Pavel Hrubeš, *On the nonnegative rank of distance matrices*, Information
Processing Letters **112** (2012), 457–461, supplies the upper-bound construction
cited there.

## Status evidence

The July 2026 revision records bounds $6\le
\operatorname{rank}_+(D)\le7$ and explicitly calls the exact value open.
Targeted searches for the nine-point linear Euclidean distance matrix and
subsequent nonnegative-rank results found no resolution. This is a named
unresolved benchmark in the source, rather than an arbitrary specialization
of a separately counted general problem.
