# MF-11 — Temporal regularity of marginal matrix-product growth

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** open; two-part question retained as one entry  
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

Does every family in this notation satisfy both

$$
\exists c>0\ \forall k,\ell\ge1:\quad
g_{\mathcal M}(k+\ell)\ge c\,g_{\mathcal M}(k)
$$

and

$$
\forall \ell\ge1\ \exists C_\ell>0\ \forall k\ge1:\quad
g_{\mathcal M}(\ell k)\le C_\ell\,g_{\mathcal M}(k)?
$$

Constants may depend on $\mathcal M$.

## Reference and status evidence

Varney and Morris,
[On marginal growth rates of matrix products](https://arxiv.org/html/2209.00449),
Linear Algebra Appl. 709 (2025), 132–163,
[DOI](https://doi.org/10.1016/j.laa.2025.01.013), §4, Definition 4.1 and §7,
Question 1. The source names these properties weak increase and weak upper regular
variation. Searches for both property names, the authors, and subsequent
matrix-product growth papers located no resolution.
