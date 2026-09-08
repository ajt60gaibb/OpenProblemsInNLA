# MF-07 — Uniform polynomial bounds for products at joint spectral radius one

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open; Conjecture L3 in the source below  
**Last checked:** 2026-09-08  

## Context and notation

Let $\mathcal H_d$ denote the nonempty compact subsets of
$\mathbb C^{d\times d}$.

The joint spectral radius of a nonempty compact set $\mathcal M\subset\mathbb C^{d\times d}$ is

$$
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
$$

This definition also applies to finite real matrix sets. The ordinary spectral
radius of one matrix is written $\rho(A)$.

## Problem statement

Does each $d\ge1$ admit $\Theta_d>0$ such that every
$\mathcal M\in\mathcal H_d$ with $\widehat\rho(\mathcal M)=1$ satisfies

$$
\|A_k\cdots A_1\|_2\le\Theta_d(Lk)^{d-1},\qquad
L=\max_{A\in\mathcal M}\|A\|_2,
$$

for all $k\ge1$ and all $A_1,\ldots,A_k\in\mathcal M$?

## Reference and status evidence

Epperlein and Wirth,
[The joint spectral radius is pointwise Hölder continuous](https://arxiv.org/html/2311.18633v2),
§2, Conjecture 3 (L3). Lemma 27 proves dimension two. The constant above must
be independent of the family.

## Common follow-up screen for [MF-05](../MF-05/README.md)–MF-07

Searches combining “joint spectral
radius” with “local Hölder”, “Lipschitz lower”, “trajectory bounds”, the authors'
names, and 2025/2026 found no later resolution. These searches supplement the
explicit 2025 conjectures; they do not establish exhaustiveness. The three entries
are separately named assertions in the source, not a count of dimensional cases.
