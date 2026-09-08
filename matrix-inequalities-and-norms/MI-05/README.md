# MI-05 — The Marcus–de Oliveira determinantal conjecture

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Last checked:** 2026-09-08

## Problem statement

For every integer $n\ge1$, let $A,B\in\mathbb C^{n\times n}$ be normal matrices, meaning $AA^*=A^*A$ and $BB^*=B^*B$. List their eigenvalues with algebraic multiplicity as $a_1,\ldots,a_n$ and $b_1,\ldots,b_n$. Is

$$\det(A+B)\in\operatorname{conv}\left\{\prod_{i=1}^n(a_i+b_{\sigma(i)}):\sigma\in S_n\right\}?$$

Here $S_n$ is the permutation group and the convex hull is taken in $\mathbb C\cong\mathbb R^2$.

## Why it matters

The conjecture would bound a determinant using only two spectra, even when the matrices are not simultaneously diagonalizable. It is a fundamental spectral enclosure problem for structured matrix computations.

## References

1. A. Kovacec, *A conjecture more precise and stronger than the one by Marcus and de Oliveira*, DMUC Preprint 26-11 (7 April 2026), §1, Conjectures 1 and 1′. [Primary paper](https://www.mat.uc.pt/preprints/ps/p2611.pdf).
2. N. Bebiano and J. P. da Providência, *Revisiting the Marcus–de Oliveira conjecture*, Mathematics 13(5) (2025), 711, §1. [DOI](https://doi.org/10.3390/math13050711).
3. J. I. Mulero-Martínez, *A variational framework for determinantal inequalities of normal matrices: Successes and obstructions*, Linear Algebra and its Applications 740 (2026), 19–38; abstract and structured-class results. [DOI](https://doi.org/10.1016/j.laa.2026.03.019).

## Status check — 2026-09-08

The April 2026 preprint proposes a stronger conjecture rather than proving this one. The July 2026 journal paper explicitly describes the unrestricted conjecture as open and proves structured cases. Searches included `Marcus de Oliveira conjecture 2026 proof`, `Marcus Oliveira determinant counterexample`, and the exact 2026 titles. No complete proof or counterexample was located. Primary full text was checked for reference 1; reference 3's status evidence was its publisher abstract, not an independently audited proof.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
