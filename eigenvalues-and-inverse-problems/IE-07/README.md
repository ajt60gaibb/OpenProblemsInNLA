# IE-07 — Deterministic regularization of the nonsymmetric eigenproblem

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** open.  
**Last checked:** 2026-09-08  

## Problem statement

For a matrix $M$ with simple spectrum, define

$$
\operatorname{gap}(M)=\min_{i\ne j}|\lambda_i(M)-\lambda_j(M)|,
\qquad
\kappa_V(M)=\inf_{M=VDV^{-1},\ D\text{ diagonal}}\|V\|_2\|V^{-1}\|_2.
$$

For every $n\geq2$, $A\in\mathbb C^{n\times n}$ with $\|A\|_2\leq1$, and $0<\delta<1/2$, construct deterministically a matrix $E$ such that

$$
\|E\|_2\leq\delta,\qquad A+E\text{ has simple spectrum},\qquad
\frac{\kappa_V(A+E)}{\operatorname{gap}(A+E)}\leq C(n/\delta)^c,
$$

using $O(n^3\log^d(n/\delta))$ exact arithmetic operations, for universal constants $C,c,d$. The task is to find the perturbation, not merely prove its existence.

## References

Banks, Garza-Vargas, Kulkarni, and Srivastava, [*Pseudospectral Shattering, the Sign Function, and Diagonalization in Nearly Matrix Multiplication Time*](https://doi.org/10.1007/s10208-022-09577-5), FOCM 23 (2023), §6, first future-research question. Amsel et al., [*Linear Systems and Eigenvalue Problems*](https://arxiv.org/html/2602.05394v3#S3.SS1), August 2026, Problem 3.1.

## Status check

Searches for `deterministic pseudospectral shattering 2026` found randomized and exponential-bound deterministic results, not the stated algorithm. The normalization and exponent orientation here are explicit: Problem 3.1's printed $(\delta/n)^c$ contradicts its own preceding motivation; $(n/\delta)^c$ is the intended polynomial upper bound.
