# MF-12 — Realizing arbitrary polynomial growth exponents by finite matrix families

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open; explicit question in a 2025 journal paper  
**Last checked:** 2026-09-08  

## Context and notation

The joint spectral radius of a nonempty compact set $\mathcal M\subset\mathbb C^{d\times d}$ is

$$
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
$$

This definition also applies to finite real matrix sets. The ordinary spectral
radius of one matrix is written $\rho(A)$.

For a compact nonempty $\mathcal M\subset\mathbb R^{d\times d}$ with
$\widehat\rho(\mathcal M)=1$, define its maximal product norm at length $k$ by

$$
g_{\mathcal M}(k)=\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2.
$$

This problem concerns growth within one family over time. [MF-07](../MF-07/README.md) instead requests
a dimension-dependent bound uniform across families.

## Problem statement

For every real $\alpha\ge0$, do there exist a positive integer
$d$, a finite nonempty $\mathcal M\subset\mathbb R^{d\times d}$ with
$\widehat\rho(\mathcal M)=1$, and constants $0<c\le C<\infty$ such that

$$
c k^\alpha\le g_{\mathcal M}(k)\le C k^\alpha
\qquad\text{for every integer }k\ge1?
$$

## Reference and status evidence

Varney and Morris,
[On marginal growth rates of matrix products](https://arxiv.org/html/2209.00449),
§7, Question 2. Corollary 6.1 realizes exponent $1/3$; the all-exponents question
remains posed. Searches for the title, authors, and marginal-growth exponents
through 2026 located no complete answer. Infinite compact families and
subsequence-only lower bounds do not meet the finite-family, every-length target.
