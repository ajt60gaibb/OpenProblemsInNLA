# MI-13 — Nobori's spectral-middle-factor commutator conjecture

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Provenance:** explicit conjecture  
**Last checked:** 2026-09-08

## Problem statement

Let $m,n\ge2$ be integers. For every $A,C\in\mathbb C^{m\times n}$ and $B\in\mathbb C^{n\times m}$, is

$$\|ABC-CBA\|_F^2\le
2\|B\|_2^2\bigl(\sigma_1(A)^2+\sigma_2(A)^2\bigr)\|C\|_F^2?$$

Here $\|X\|_F=(\operatorname{tr}(X^*X))^{1/2}$, $\|X\|_2=\sigma_1(X)$, and $\sigma_1(X)\ge\sigma_2(X)\ge\cdots$ are the singular values. Zero matrices and deficient ranks are allowed.

## Relevance

The expression measures failure of two rectangular factors to commute through a middle map. A bound using the middle factor's operator norm and only two singular values of an outer factor would sharpen estimates for products of rectangular matrices.

## References

1. M. Nobori, *A generalization of the Böttcher–Wenzel inequality for three rectangular matrices*, Linear Algebra and its Applications 725 (2025), 135–144. Conjecture 3.1, equation (8), in [arXiv:2506.17365v2](https://arxiv.org/html/2506.17365v2); [journal](https://doi.org/10.1016/j.laa.2025.07.005).
2. M. Nobori, *A note on some upper bounds for the Frobenius norm of the $q$-deformed commutator*, arXiv:2608.03897v1 (2026), Theorem 1.1 and §3. [Primary manuscript](https://arxiv.org/html/2608.03897v1).

## Status check — 2026-09-08

The original arXiv record remains v2, dated 3 July 2025. Its proved Theorem 1.1 places the spectral norm on $C$ and the Frobenius norm on $B$; that is a different assertion. The author's August 2026 paper treats two-factor expressions $AB-qBA$, and does not claim this conjecture. Searches used `Nobori Conjecture 3.1`, `three rectangular matrices conjecture proof`, and `Nobori commutator spectral conjecture`. No resolution was located. The original conjecture and later theorem statements were inspected; the subscription journal body was not independently retrieved.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
