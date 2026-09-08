# MI-17 — The Lih–Wang permanent inequality toward the flat matrix

**Difficulty:** extreme  
**Importance:** interesting to specialist  
**Provenance:** explicit conjecture  
**Last checked:** 2026-09-08

## Problem statement

For every integer $n\ge3$, let $A=(a_{ij})\in\mathbb R^{n\times n}$ be doubly stochastic: $a_{ij}\ge0$ and every row and every column has sum one. Put $J_n=\mathbf1\mathbf1^T/n$, with $\mathbf1\in\mathbb R^n$ the all-ones vector. Is

$$\operatorname{per}\bigl(tJ_n+(1-t)A\bigr)
\le t\operatorname{per}(J_n)+(1-t)\operatorname{per}(A)
\qquad\text{for every }t\in[1/2,1]?$$

Here $\operatorname{per}(C)=\sum_{\sigma\in S_n}\prod_{i=1}^n c_{i,\sigma(i)}$, so $\operatorname{per}(J_n)=n!/n^n$. Neither symmetry nor positive semidefiniteness is assumed for $A$.

## Relevance

Mixing with the flat matrix is a basic averaging operation on stochastic matrices. The conjecture asks for a sharp bound on the permanent along a specified part of each such segment.

## References

1. K.-W. Lih and E. T. H. Wang, *A convexity inequality on the permanent of doubly stochastic matrices*, Congressus Numerantium 36 (1982), 189–198. Original statement and order-three result; bibliographic attribution and formulation reproduced in reference 2, §1.
2. D. K. Udayan and K. Somasundaram, *Lih Wang's and Dittert's conjectures on permanents*, Special Matrices 12 (2024), 20240006, §1, equation (3), Theorems 2.1–2.2. [Published full text](https://www.degruyterbrill.com/document/doi/10.1515/spma-2024-0006/html); [older arXiv v1](https://arxiv.org/abs/2312.00464).

## Status check — 2026-09-08

The arXiv record remains its December 2023 v1, but the May 2024 published paper has materially narrower claims than that preprint's abstract. Published Theorem 2.1 covers order four; Theorem 2.2 covers only certain order-six matrices and $t\in[0.7836,1]$. The general-dimensional assertion survives. Searches used `Lih Wang conjecture 2026 permanent`, `Lih-Wang permanent counterexample proof 2025 2026`, and the exact journal title. No full resolution was located. The full journal theorem statements were read; the 1982 paper was traced through their references. The failed extension to all $t\in[0,1]$ is a different assertion.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
