# IS-04 — A condition number of two for a sign matrix in every dimension

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open.  
**Last checked:** 2026-09-08  

## Problem statement

For $n\geq1$, define

$$
h(n)=\min_{A\in\{-1,1\}^{n\times n}}\kappa_2(A),\qquad
\kappa_2(A)=\frac{\sigma_{\max}(A)}{\sigma_{\min}(A)},
$$

with $\kappa_2(A)=+\infty$ for singular $A$. Prove or disprove

$$
\sup_{n\geq1}h(n)=2.
$$

Since $h(3)=2$, the unresolved claim is the upper bound in every dimension.
No symmetry or circulant structure is imposed. The target refines the known
existence of uniformly well-conditioned sign matrices, which is useful for
constructing approximately isometric linear maps and well-conditioned bases.

## References

Alexeev, Jasper, and Mixon,
[*Asymptotically optimal approximate Hadamard matrices*](https://arxiv.org/html/2511.14653v1),
§6, Problem 12. Dong and Rudelson,
[*Approximately Hadamard matrices and Riesz bases in random frames*](https://arxiv.org/abs/2207.07523),
introduction; *IMRN* (2024), 2044–2065.

## Status check

Searches for `approximate Hadamard sup 2 conjecture`,
`2511.14653 2026 condition number`, and `approximate Hadamard supremum`
found no proof of the sharp constant. The fact that $h(n)\to1$ is already
known and is not the problem counted here.
