# MF-05 — Local Hölder continuity of the joint spectral radius

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open; Conjecture L1 in the source below  
**Last checked:** 2026-09-08  

## Context and notation

Let $\mathcal H_d$ denote the nonempty compact subsets of
$\mathbb C^{d\times d}$. Use the spectral norm and its Hausdorff distance

$$
d_H(\mathcal M,\mathcal N)=\max\left\{
\sup_{A\in\mathcal M}\inf_{B\in\mathcal N}\|A-B\|_2,
\sup_{B\in\mathcal N}\inf_{A\in\mathcal M}\|A-B\|_2\right\}.
$$

The joint spectral radius is

$$
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
$$

These definitions also apply to finite real matrix sets. The ordinary spectral
radius of one matrix is written $\rho(A)$.

## Problem statement

For every $d\ge1$ and $\mathcal M_0\in\mathcal H_d$, do
there exist $r,C>0$ such that

$$
|\widehat\rho(\mathcal M)-\widehat\rho(\mathcal N)|
\le C d_H(\mathcal M,\mathcal N)^{1/d}
$$

whenever $d_H(\mathcal M,\mathcal M_0)<r$ and
$d_H(\mathcal N,\mathcal M_0)<r$?

## Reference and status evidence

Epperlein and Wirth,
[The joint spectral radius is pointwise Hölder continuous](https://arxiv.org/html/2311.18633v2),
Linear Algebra Appl. 704 (2025), 92–122,
[DOI](https://doi.org/10.1016/j.laa.2024.09.016), §2, Conjecture 3 (L1).
Pointwise results in that paper do not prove this local assertion.

## Additional status evidence

Searches combining “joint spectral
radius” with “local Hölder”, “Lipschitz lower”, “trajectory bounds”, the authors'
names, and 2025/2026 found no later resolution. These searches supplement the
explicit 2025 conjectures; they do not establish exhaustiveness. The three entries
are separately named assertions in the source, not a count of dimensional cases.
