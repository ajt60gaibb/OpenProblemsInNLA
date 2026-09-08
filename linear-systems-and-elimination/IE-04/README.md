# IE-04 — Exponential smoothed tail bounds for partial pivoting

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** open.  
**Last checked:** 2026-09-08  

## Context and notation

All elimination in this problem is in exact arithmetic. Write $\|A\|_{\max}=\max_{ij}|a_{ij}|$. A pivoting path creates successive active Schur complements $S_1=A,S_2,\ldots,S_n$, with row/column permutations as appropriate. Its element-growth factor is

$$
\rho(A)=\frac{\max_{1\leq j\leq n}\|S_j\|_{\max}}{\|A\|_{\max}}.
$$

Partial pivoting chooses a largest-magnitude entry in the active first column; complete pivoting chooses one anywhere in the active matrix. If ties occur, a universal statement includes every admissible tie choice; a supremum includes all admissible paths. These conventions remove implementation-dependent ambiguity. Matrices are nonsingular unless otherwise stated.

## Problem statement

Do universal constants $c_1,c_2>0$ exist such that, for every $n\geq1$, deterministic $\bar A\in\mathbb R^{n\times n}$ with $\|\bar A\|_2\leq1$, $0<\sigma\leq1$, and $x\geq1$, the matrix $A=\bar A+\sigma G$, with independent standard normal entries in $G$, satisfies

$$
\Pr\!\left\{\rho_{\mathrm{PP}}(A)>x(n/\sigma)^{c_1}\right\}
\leq 2^{-c_2x}?
$$

This is a uniform smoothed-analysis question: the deterministic center may itself be a worst-case input. Almost surely the perturbed matrix is nonsingular and the pivot choices have no ties. Numerical evidence or estimates only at $\bar A=0$ do not settle the quantifier over deterministic centers. The tail estimate would quantify the rarity of substantial growth after small Gaussian input perturbations.

## References

Spielman and Teng, [*Smoothed Analysis: An Attempt to Explain the Behavior of Algorithms in Practice*](https://www.cs.yale.edu/homes/spielman/PAPERS/focmSmoothed.pdf), §P6, Conjecture 16, p. 52 of the author PDF. Huang and Tikhomirov, [*Average-case analysis of the Gaussian elimination with partial pivoting*](https://doi.org/10.1007/s00440-024-01276-2), PTRF 189 (2024), introduction.

## Status check

Searches for `Exponential Stability of GEPP solved` and `Gaussian elimination smoothed analysis 2025 2026` found the average-case theorem, not this exponential tail bound. The 2026 Peca-Medlin butterfly paper also distinguishes average-case results from the still-unavailable full smoothed analysis. Randomizing the pivot rule is a different model.
