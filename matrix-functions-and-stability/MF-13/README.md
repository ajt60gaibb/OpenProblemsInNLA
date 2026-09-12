# MF-13 — Symmetric maximizers for Lyapunov operators of order six

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because the last undecided dimension sits between proved cases and counterexamples; specialist impact reflects the surviving order-six norm identity rather than the refuted all-orders claim.  
**Last checked:** 2026-09-10  
**Status:** Open  

## Problem statement

For each real matrix $`A\in\mathbb R^{6\times6}`$, define $`L_A(X)=AX+XA^T`$. Write $`\|X\|_F=(\mathop{\mathrm{tr}}\nolimits(X^TX))^{1/2}`$. Is it true that

```math
\max_{X\in\mathbb R^{6\times6},\ \|X\|_F=1}\|L_A(X)\|_F
=
\max_{X=X^T,\ \|X\|_F=1}\|L_A(X)\|_F
\qquad\text{for every }A\in\mathbb R^{6\times6}?
```

This concerns the **largest** singular value of the Lyapunov operator, with no stability assumption on $`A`$.

## Why it matters

Restricting a norm calculation to symmetric matrices substantially reduces the associated singular-value problem. The conjecture asks when that reduction retains the exact operator norm, an issue relevant to matrix-equation norm estimation.

## References

1. D. Kressner and B. Vandereycken, *A counterexample to the symmetric-maximizer conjecture for Lyapunov operators*, arXiv:2608.20875v1, 21 August 2026, §§1 and 5. [Primary text](https://arxiv.org/html/2608.20875).
2. R. Byers and S. Nash, *On the singular “vectors” of the Lyapunov operator*, SIAM Journal on Algebraic and Discrete Methods 8(1) (1987), 59–66. [DOI](https://doi.org/10.1137/0608003).

## Status check — 2026-09-08

Reference 1 explicitly leaves order six open, while refuting every order at least seven. The original all-orders assertion must therefore not be catalogued as open. The latest arXiv record is v1. Searches included `symmetric-maximizer Lyapunov order six`, `Lyapunov conjecture 2026 proof`, and the exact paper title; no subsequent resolution of order six was located. This is a targeted literature check, not a certification of openness.

## Audit — 2026-09-10

Rechecked the [August 2026 counterexample paper, §5](https://arxiv.org/html/2608.20875): order six alone remains unresolved. Exact-title and order-six searches found no subsequent resolution. The importance rating now reflects this narrow surviving target; the broader symmetric-maximizer assertion has already been refuted.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
