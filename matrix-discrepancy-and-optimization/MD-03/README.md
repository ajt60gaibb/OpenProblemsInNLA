# MD-03 — The Komlós discrepancy conjecture

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Provenance:** source-stated conjecture.  
**Last checked:** 2026-09-08

**Status:** no resolution found in screening on 2026-09-08.  

Does a finite constant $C>0$ exist such that, for every pair of positive integers $m,n$ and every matrix $A=(a_{ij})\in\mathbb R^{m\times n}$ satisfying
$$
\sum_{i=1}^m a_{ij}^2\leq1\qquad(1\leq j\leq n),
$$
there is a vector $x\in\{-1,1\}^n$ for which
$$
\|Ax\|_\infty=\max_{1\leq i\leq m}\left|\sum_{j=1}^n a_{ij}x_j\right|\leq C?
$$
The same constant must work for every dimension and matrix. The question asks for existence of a signing; it does not additionally require an algorithm.

This is a matrix balancing problem: choose column signs so that their sum is small in every coordinate. Its norm constraint and simultaneous coordinate control connect discrepancy theory with rounding and linear optimization.

## References

1. N. Bansal and H. Jiang, *An Exposition of the $\widetilde O(\log^{1/4}n)$ Bound for the Komlós Problem*, arXiv:2608.28452 (2026), abstract and introduction, including the explicit conjecture and the new dimension-dependent bound. [Paper](https://arxiv.org/html/2608.28452v1).
2. N. Bansal and H. Jiang, *Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlós Bounds Beyond Banaszczyk*, arXiv:2508.03961v2 (2025), abstract and introductory results. [Paper](https://arxiv.org/abs/2508.03961).
3. W. Banaszczyk, *Balancing vectors and Gaussian measures of n-dimensional convex bodies*, Random Structures & Algorithms 12(4) (1998), pp. 351–360, the main vector-balancing theorem underlying the earlier logarithmic bound. [Article](https://onlinelibrary.wiley.com/doi/abs/10.1002/%28SICI%291098-2418%28199807%2912%3A4%3C351%3A%3AAID-RSA3%3E3.0.CO%3B2-S).

## Status check — 2026-09-08

checked the current arXiv records (2608.28452v1, 2026-08-28; 2508.03961v2, 2025-09-09) and searched “Komlos conjecture solved proof September 2026” and “Komlos Bansal Jiang 2026 bound”. The new bound is $O((\log n)^{1/4}(\log\log n)^{7/4})$ in its asymptotic range, not a universal constant. No full proof, counterexample, or withdrawal of these source papers was found. The disproved Hajela conjecture and the separate matrix Spencer conjecture are not this statement.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
