# MI-09 — Sharp Schatten triangle constants for the arithmetic symmetric modulus

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Last checked:** 2026-09-08

## Problem statement

For $X\in\mathbb C^{n\times n}$ set $S(X)=((X^*X)^{1/2}+(XX^*)^{1/2})/2$. Let $\|X\|_p=(\sum_i\sigma_i(X)^p)^{1/p}$ for $1\le p<\infty$, with $\|X\|_\infty=\sigma_1(X)$. Determine, for all integers $m,n\ge2$ and all $p\in[1,\infty]$, the exact value

$$c_p^{\rm sym}(m,n)=\sup_{(A_1,\ldots,A_m)\ne(0,\ldots,0)}
\frac{\|S(A_1+\cdots+A_m)\|_p}{\|S(A_1)+\cdots+S(A_m)\|_p},
\qquad A_j\in\mathbb C^{n\times n}.$$

The denominator is positive on the stated domain. A resolution should identify the value for the unsolved parameters while retaining known endpoint values.

## Why it matters

This asks how much the symmetric positive representative of a matrix sum can exceed the sum of the individual representatives in Schatten norm. Sharp constants quantify the loss in this way of bounding nonnormal matrix sums.

## References

1. T. Zhang, *Operator symmetric moduli and sharp triangle inequalities*, arXiv:2603.01046v1 (1 March 2026), Problem 1.17 and §8. [Primary text](https://arxiv.org/html/2603.01046).
2. J.-C. Bourin and E.-Y. Lee, *Some hybrid matrix triangle inequalities*, arXiv:2606.29188v1 (28 June 2026), introduction and Theorem 1.3, for the dimension-independent majorization bound. [Primary text](https://arxiv.org/html/2606.29188).

## Status check — 2026-09-08

The source proves $c_1^{\rm sym}=1$ and $c_\infty^{\rm sym}=\sqrt2$ when $n\ge3$, and gives bounds for the other cases. Its latest version remains v1. Searches included `arithmetic symmetric modulus optimal Schatten constants`, `Zhang Problem 1.17 symmetric modulus`, and both paper titles with `2026 sharp`. No general determination was found. Problem 1.11's two-dimensional restriction is subsumed here and is not counted as an additional entry. Unlike the unitary-orbit conjecture, this problem asks for exact norm extrema, not a positive-semidefinite domination.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
