# PF-03 — Rational factors for rational completely positive boundary matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** open; checked 2026-09-08  
**Area:** exact certificates for nonnegative symmetric factorization  
**Last checked:** 2026-09-08  

## Context and notation

A symmetric matrix $A$ is **completely positive** if $A=BB^\mathsf T$ for an entrywise nonnegative real matrix $B$ with finitely many columns. Let $\mathcal{CP}_n$ be the cone of these matrices of order $n$. Its **cp-rank**, $\operatorname{cpr}(A)$, is the minimum number of columns in such a factor, with $\operatorname{cpr}(0)=0$. Boundaries and interiors use the usual Euclidean topology on the vector space of real symmetric matrices.

## Problem statement

For every integer $n\ge5$ and every

$$
A\in\mathbb Q^{n\times n}\cap\partial\mathcal{CP}_n,
$$

does there exist a finite integer $m\ge1$ and a matrix $B\in\mathbb Q_{\ge0}^{n\times m}$ such that

$$
A=BB^\mathsf T?
$$

The width $m$ is unrestricted. In particular, it need not equal the real cp-rank or the order of $A$. This is an existence question for an exact rational certificate of complete positivity.

Rational matrices in the interior of $\mathcal{CP}_n$ have rational completely positive factors. Several boundary classes are also known, including matrices of rank at most two. The question concerns the remaining boundary matrices.

## References

Abraham Berman and Naomi Shaked-Monderer, [*Completely Positive Matrices over Sets*](https://cot.mathres.org/issues/COT202523.pdf), Communications in Optimization Theory (2025), article 23, §2, Question 2.1 and the explicit boundary Open Problem, p. 2. Mathieu Dutour Sikirić, Achill Schürmann, and Frank Vallentin, [*Rational factorizations of completely positive matrices*](https://doi.org/10.1016/j.laa.2017.02.017), Linear Algebra and its Applications **523** (2017), 46–51, Theorem 1.1. Max Pfeffer and José Alejandro Samper, [*The Cone of $5\times5$ Completely Positive Matrices*](https://link.springer.com/article/10.1007/s00454-023-00620-y), Discrete & Computational Geometry **71** (2024), 442–466, §6, Problem 6.3, discusses the order-five boundary.

## Status evidence

Searches for “rational completely positive 2026 boundary” and “completely positive rational 2025” located no general boundary resolution. Alexander Oertel and Achill Schürmann's [*Generalized Perfect Matrices*, latest arXiv v2](https://arxiv.org/html/2602.05841v2), submitted 2026-06-04, §6.1.1, still guarantees rational factors for interior matrices; its introduction describes the general rational-factorization algorithm conditionally on existence. Neither result resolves the displayed boundary question.
