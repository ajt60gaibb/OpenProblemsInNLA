# SP-06 — A real-valued symbol on a Jordan curve and real Toeplitz spectra

**Topic:** Spectra of finite banded Toeplitz matrices.  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Last checked:** 2026-09-08

## Problem statement

Let $r,s\ge1$ be integers and

$$
b(z)=\sum_{k=-r}^{s}b_kz^k,
\qquad b_k\in\mathbb C,\qquad b_{-r}b_s\ne0.
$$

For every $n\ge1$, define $T_n(b)=(b_{i-j})_{i,j=1}^n$, with $b_k=0$ outside $[-r,s]$. Suppose there is a Jordan curve $\gamma\subset\mathbb C\setminus\{0\}$ such that $b(z)\in\mathbb R$ for every $z\in\gamma$. A Jordan curve means the image of a continuous injective map from the unit circle.

Must

$$
\operatorname{spec}(T_n(b))\subset\mathbb R
\qquad\text{for every integer }n\ge1?
$$

## Why it matters

The conjecture would characterize a broad source of real spectra in nonsymmetric structured eigenvalue problems through a scalar symbol condition, uniformly over matrix size.

## References

- B. Shapiro and F. Štampach, [Non-Self-Adjoint Toeplitz Matrices Whose Principal Submatrices Have Real Spectrum](https://arxiv.org/abs/1702.00741), *Constructive Approximation* 49 (2019), 191–226. Equation (2), Theorem 1(ii)–(iii), and Theorem 8; use arXiv v4, which includes the correction.
- B. Shapiro and F. Štampach, [Correction to the same article](https://doi.org/10.1007/s00365-022-09614-0), 2023. The correction, pp. 27–28 of the combined arXiv PDF, withdraws the proof of (ii)$\Rightarrow$(iii) and explicitly proposes the implication as conjectural.
- D. Giandinoto, [On reality of eigenvalues of banded block Toeplitz matrices](https://arxiv.org/abs/2411.16266), 2024, introduction and §2. The paper describes the corrected scalar implication as a conjecture before considering a block generalization.

## Status check

On 2026-09-08, checked the corrected arXiv v4 (2022-12-29), its appended erratum, and Giandinoto's November 2024 paper. Searches combined “Shapiro”, “Štampach”, “Toeplitz”, “reality”, “erratum”, “Jordan curve”, “proof”, and 2026. No general resolution was located. The original article's theorem label is misleading without its correction: the finite-spectrum implication above remains the authors' stronger proposed statement. Its weaker limiting-spectrum consequence and particular symbol families are not separate catalog problems here.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
