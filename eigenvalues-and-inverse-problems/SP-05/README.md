# SP-05 — Symmetric minimizer for a positive definite Jordan–Kronecker product

**Topic:** Structured eigenvalue problems and semidefinite optimization.  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Last checked:** 2026-09-08

## Problem statement

Let $n\ge 2$ and let $A,B\in\mathbb R^{n\times n}$ be symmetric positive definite. Let $T\in\mathbb R^{n^2\times n^2}$ be the commutation matrix defined by $T\operatorname{vec}(X)=\operatorname{vec}(X^T)$, where $\operatorname{vec}$ stacks columns. Is it always true that

$$
\min_{\substack{u\in\mathbb R^{n^2}\setminus\{0\}\\Tu=u}}
\frac{u^T(A\otimes B)u}{u^Tu}
\;\le\;
\min_{\substack{w\in\mathbb R^{n^2}\setminus\{0\}\\Tw=-w}}
\frac{w^T(A\otimes B)w}{w^Tw}?
$$

Equivalently, must the smallest eigenvalue of $A\otimes B+B\otimes A$ have an eigenvector $\operatorname{vec}(X)$ with $X=X^T\ne0$?

## Why it matters

An affirmative answer would identify which invariant subspace contains the smallest eigenvalue of an important structured matrix operator, relevant to positivity checks in semidefinite optimization.

## References

- N. Kalantarova and L. Tunçel, [On the spectral structure of Jordan–Kronecker products of symmetric and skew-symmetric matrices](https://arxiv.org/abs/1805.09737), *Linear Algebra and its Applications* 608 (2021), 343–362. Conjecture 1, equation (7), p. 12 of arXiv v3; the preceding discussion explains the optimization connection.
- D. Kressner and B. Vandereycken, [A counterexample to the symmetric-maximizer conjecture for Lyapunov operators](https://arxiv.org/abs/2608.20875), 2026, abstract. This resolves a different symmetric-maximizer conjecture and is included to distinguish the recent result from this problem.

## Status check

On 2026-09-08, checked arXiv v3 (2020-08-08, still the latest listed version) and searched combinations of “Jordan-Kronecker”, “positive definite”, “conjecture”, “smallest”, “counterexample”, and the authors' names, including 2025–2026 results. No resolution of Conjecture 1 was located. The source's counterexamples to general symmetric-matrix interlacing do not dispose of its separately stated positive definite conjecture. The August 2026 Lyapunov result concerns an operator norm maximizer, rather than this positive definite Jordan–Kronecker minimum. No recent explicit reaffirmation of this exact conjecture was found; the status evidence is therefore bounded.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
