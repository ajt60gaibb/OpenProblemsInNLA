# MI-15 — A sum-of-squares representation for the Toeplitz commutator form

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Provenance:** explicit conjecture  
**Last checked:** 2026-09-08

## Problem statement

For an integer $n\ge2$, let $x_{-(n-1)},\ldots,x_{n-1},y_{-(n-1)},\ldots,y_{n-1}$ be independent real variables. Form real Toeplitz matrices $X=(x_{i-j})_{i,j=1}^n$ and $Y=(y_{i-j})_{i,j=1}^n$, and the homogeneous quartic polynomial

$$F_n(x,y)=2\|X\|_F^2\|Y\|_F^2
-2\bigl(\operatorname{tr}(X^TY)\bigr)^2-\|XY-YX\|_F^2,$$

where $\|Z\|_F^2=\sum_{i,j}z_{ij}^2$ for real matrices. Is it true that for every $n\ge2$ there are a finite integer $N_n\ge0$ and homogeneous quadratic polynomials $q_{n,1},\ldots,q_{n,N_n}$ with real coefficients in these $4n-2$ variables such that

$$F_n(x,y)=\sum_{j=1}^{N_n}q_{n,j}(x,y)^2$$

as a polynomial identity? The polynomials may depend on $n$. Rational coefficients are not required.

## Relevance

An explicit sum-of-squares identity would give an algebraic certificate for a structured matrix inequality and connects Toeplitz calculations to semidefinite optimization. Nonnegativity alone does not answer this question.

## References

1. L. László, *Sum of squares representation for the Böttcher–Wenzel biquadratic form*, Acta Universitatis Sapientiae, Informatica 4(1) (2012), 17–32: equation (1), §5, and Conjecture 15, p.31. [Primary manuscript](https://arxiv.org/pdf/1207.6372).
2. J. Ge, F. Li, Z. Tang, and Y. Zhou, *A survey on the DDVV-type inequalities*, Advances in Mathematics (China) 53 (2024), 449–467: published Conjecture 4.1, p.461; Conjecture 4.3 in [arXiv:2402.01085v1](https://arxiv.org/html/2402.01085v1). [Published PDF](https://ccj.pku.edu.cn/Article/DownLoad?id=374327987&type=ArticleFile).

## Status check — 2026-09-08

Both arXiv records remain v1; the published 2024 survey still poses this SOS assertion. László's particular certificate strategy works through order seven; its failure in a larger order is not a disproof of all SOS representations. Searches used `Toeplitz SOS Wenzel`, `Toeplitz Bottcher squares proof`, and `Toeplitz Conjecture 15 squares`. No general proof or non-SOS counterexample was located. The already proved Böttcher–Wenzel nonnegativity statement is not being counted again. The optional rational-certificate request in the original is not imposed as an additional conjecture.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
