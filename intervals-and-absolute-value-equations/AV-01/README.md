# AV-01 — Recognizing the maximum finite number of solutions

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** open; checked 2026-09-08  
**Area:** complexity of piecewise linear systems  
**Last checked:** 2026-09-08  

## Context and notation

Absolute values and vector inequalities are componentwise. All algorithmic questions use rational input in binary and the deterministic Turing model. Input length includes the matrix dimensions and the bit lengths of all rational coefficients.

## Problem statement

For input $A\in\mathbb Q^{n\times n}$ and $b\in\mathbb Q^n$, $n\ge1$, set

$$
\Sigma_+(A,b)=\{x\in\mathbb R^n:Ax+|x|=b\}.
$$

### Question

Classify the computational complexity of deciding whether

$$
|\Sigma_+(A,b)|=2^n.
$$

In particular, is this decision problem in $\mathsf P$, or can an $\mathsf{NP}$-hardness or $\mathsf{coNP}$-hardness classification be established by polynomial-time many-one reductions? The task returns one Boolean answer. Infinite solution sets are negative instances. There is no promise that the solution set is finite.

## Reference

Milan Hladík, [*Absolute value equations with $2^n$ solutions*](https://doi.org/10.1007/s11590-025-02251-z), Optimization Letters **20** (2026), 559–575, §2.3 and §7. The paper provides structural characterizations but explicitly leaves this recognition complexity open. Proposition 9 treats the subclass $\rho(|A|)<1$.

## Status evidence

The version of record appeared October 6, 2025, in the April 2026 issue. Searches for the title with “complexity”, “solved”, and “2026”, and for “Hladík $2^n$ complexity”, found no subsequent classification. No separate arXiv version was located. The related result about more than $2^{n-1}$ solutions concerns a different threshold and does not settle this question.
