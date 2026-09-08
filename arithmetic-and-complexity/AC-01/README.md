# AC-01 — Is the matrix multiplication exponent two?

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Topic:** arithmetic complexity of dense matrix multiplication  
**Last checked:** 2026-09-08  
**Status:** open; admitted after a bounded literature search found no resolution.  

## Problem statement

Over the field $\mathbb C$, let $M(n)$ be the minimum number of
scalar additions, subtractions, multiplications, and divisions in an arithmetic
straight-line program computing every entry of $AB$ for arbitrary
$A,B\in\mathbb C^{n\times n}$. Programs must be defined on their intended inputs.
Set $\omega=\inf\{\tau:M(n)=O(n^\tau)\}$. Is $\omega=2$? Equivalently, for every
$\varepsilon>0$, can these products be computed in $O(n^{2+\varepsilon})$
arithmetic operations? This asks about asymptotic arithmetic cost; it does not
assert an $O(n^2)$ algorithm or a floating-point stability guarantee.

## Why it matters

Matrix multiplication is a basic cost driver for dense NLA.

## References and status

M. Bläser, [*Fast Matrix Multiplication*](https://theoryofcomputing.org/articles/gs005/gs005.pdf),
Graduate Surveys 5 (2013), §§1, 5, provides the computational model. E. Dupont
et al., [*Improving the matrix multiplication exponent with modern optimization
and AlphaEvolve*](https://arxiv.org/abs/2608.16884) (2026), abstract and §1,
reports $\omega<2.371177$, which does not reach two. Searches for “matrix
multiplication exponent 2026” and “omega equals 2 proof” located improvements,
not a resolution. **Admitted: no resolution located.**
