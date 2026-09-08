# AV-02 — Hardness of the spectral-norm condition number

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open; checked 2026-09-08  
**Area:** condition estimation and rigorous error bounds  
**Last checked:** 2026-09-08  

## Context and notation

Absolute values and vector inequalities are componentwise. All algorithmic questions use rational input in binary and the deterministic Turing model. Input length includes the matrix dimensions and the bit lengths of all rational coefficients.

For a real square matrix $A$, define the diagonal perturbation family

$$
\mathcal D(A)=\{A-\operatorname{diag}(d):d\in[-1,1]^n\}.
$$

Call this family **regular** when every member is nonsingular. Only diagonal entries vary. This is precisely the entrywise interval matrix $[A-I_n,A+I_n]$.

## Problem statement

Let $n\ge1$ and let $A\in\mathbb Q^{n\times n}$ be promised to have regular $\mathcal D(A)$. Define

$$
c_2(A)=\max_{d\in[-1,1]^n}
\left\|(A-\operatorname{diag}(d))^{-1}\right\|_2
=\left(\min_{d\in[-1,1]^n}
\sigma_{\min}(A-\operatorname{diag}(d))\right)^{-1}.
$$

### Question

Is deciding $c_2(A)\ge t$, given such an $A$ and a positive rational threshold $t$, $\mathsf{NP}$-hard under polynomial-time Turing reductions that query only inputs satisfying the regularity promise?

This is a decision formulation of the published hardness conjecture. Equality belongs to the yes case. Checking the promise is outside the task. The spectral norm is the operator norm induced by the Euclidean vector norm.

## References

Moslem Zamani and Milan Hladík, [*Error bounds and a condition number for the absolute value equations*](https://doi.org/10.1007/s10107-021-01756-6), Mathematical Programming **198** (2023), 85–113, §2, paragraph before Proposition 3; §2.1 and §7. The maximum is attained at a sign vector by Proposition 2; Proposition 6 gives a formula for symmetric $A$. The conjecture concerns general matrices.

The quantity bounds forward error by residual for $Ax-|x|=b$; see Theorem 7. Its computation remains explicitly unclassified in Hladík et al.'s [2026 survey](https://doi.org/10.1007/s10589-025-00717-5), §5.4.

## Status evidence

The original paper's latest arXiv version is [v2, January 17, 2020](https://arxiv.org/abs/1912.12904); the journal text was published January 30, 2022. Searches for “absolute value equations condition number 2026”, “spectral norm complexity”, and “2-norm NP-hard” found no resolution.
