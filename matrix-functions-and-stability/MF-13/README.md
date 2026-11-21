# MF-13 — Symmetric maximizers for Lyapunov operators of order six

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Historical rating of the original open target. Challenging because the last undecided dimension sits between proved cases and counterexamples; specialist impact reflects the surviving order-six norm identity rather than the refuted all-orders claim.  
**Last checked:** 2026-11-21  
**Status:** Solution claimed  

> **Affirmative solution claimed (2026-11-21).** Shanmu Jin's
> [*Symmetric maximizers of Lyapunov operators*](../../references/jin-mf13-2026-11-21/manuscript.pdf),
> Theorem 1 (p. 1) and the order-six proof in Section 3 (pp. 2–4), give an
> affirmative answer over all real order-six coefficient matrices. The
> [Lean evidence](#lean-proof-and-verification-evidence) includes attainment
> and equality of both maxima for the original target.

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

3. Shanmu Jin, *Symmetric maximizers of Lyapunov operators*, Theorem 1 and Section 3. [Manuscript PDF](../../references/jin-mf13-2026-11-21/manuscript.pdf) · [LaTeX source](../../references/jin-mf13-2026-11-21/manuscript.tex).

## Status check — 2026-09-08

Reference 1 explicitly leaves order six open, while refuting every order at least seven. The original all-orders assertion must therefore not be catalogued as open. The latest arXiv record is v1. Searches included `symmetric-maximizer Lyapunov order six`, `Lyapunov conjecture 2026 proof`, and the exact paper title; no subsequent resolution of order six was located. This is a targeted literature check, not a certification of openness.

## Audit — 2026-09-10

Rechecked the [August 2026 counterexample paper, §5](https://arxiv.org/html/2608.20875): order six alone remains unresolved. Exact-title and order-six searches found no subsequent resolution. The importance rating now reflects this narrow surviving target; the broader symmetric-maximizer assertion has already been refuted.


## Lean proof and verification evidence

The [published Lean project](https://github.com/jinshanmu/SymmetricMaximizer/tree/9a1cedcf3bec473a322b45d770bedeac7050dbb9/Lean)
pins Lean v4.36.0 and [mathlib v4.36.0](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842).

At dimension six,
`SymmetricMaximizer.symmetric_maximizers_all_orders` gives a symmetric
Frobenius-unit matrix that attains the whole operator norm for every real
coefficient matrix.

The [exact target check](../../references/jin-mf13-2026-11-21/verification/MF13Check.lean)
uses real $`6\times6`$ matrices, ordinary transpose, and the operator
$`X\mapsto AX+XA^T`$. The declaration
`MF13Verification.frobenius_norm_eq_sqrt_trace` identifies the scoped matrix
norm with the trace formula above. `MF13Verification.common_maximum`
establishes attainment and a common greatest value on both unit domains.
`MF13Verification.equal_maxima` then states the equality as an equality of
suprema. The coefficient matrix is unrestricted.

The submitter reran the build, linter and exact target check at the pinned
revision. The transitive axiom report lists only `propext`,
`Classical.choice` and `Quot.sound` for the checked declarations.
Independent catalog review is pending. [Reproduction commands](../../references/jin-mf13-2026-11-21/README.md#reproduce-the-lean-check) ·
[Dated verification log](../../references/jin-mf13-2026-11-21/verification/2026-11-21.txt)

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
