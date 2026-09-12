# KE-02 — Construct a separating diagonal perturbation in nearly linear time

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** Hermitian eigenproblems; deterministic regularization  
**Last checked:** 2026-09-10  
**Status:** Open  

**Rating rationale:** Challenging reflects derandomizing eigenvalue separation within a nearly linear cost; community impact is deterministic preprocessing for Hermitian eigensolvers.

## Context and notation

All norms are Euclidean vector norms or their induced matrix norms.

## Problem statement

For a Hermitian matrix $`H`$ with eigenvalues listed with multiplicity, define

```math
\mathop{\mathrm{gap}}\nolimits(H)=\min_{i\ne j}|\lambda_i(H)-\lambda_j(H)|.
```

Do universal constants $`a,c_0,C,q>0`$ and a deterministic algorithm exist with
the following property? For every $`n\geq2`$, Hermitian tridiagonal
$`T\in\mathbb C^{n\times n}`$ with $`\|T\|_2\leq1`$, and
$`\delta\in(0,1/2)`$, the algorithm receives the three diagonals and returns
a real diagonal matrix $`D`$ such that

```math
\|D\|_2\leq\delta,
\qquad
\mathop{\mathrm{gap}}\nolimits(T+D)\geq c_0(\delta/n)^a,
```

using at most $`Cn[1+\log(n/\delta)]^q`$ exact arithmetic operations and
comparisons? Square roots of nonnegative real numbers are allowed at unit
cost; extracting bits from exact real inputs is not.

This selects the explicitly proposed nearly linear version of the
deterministic Minami problem. It preserves tridiagonal structure and requires
only the perturbation as output. Its diagonal restriction and cost target
make it distinct from the general, cubic-cost regularization question [IE-07](../IE-07/README.md).

## References

Amsel et al., [workshop report](https://arxiv.org/html/2602.05394v3#S3.SS1),
Problem 3.2. Sobczyk, [*Deterministic complexity analysis of Hermitian eigenproblems*](https://arxiv.org/html/2410.21550v2),
§1.1 for the arithmetic model, Theorem 1.1 for the tridiagonal eigensolver,
and §5, question 4, for deterministic spectral separation.

## Earlier status check — 2026-09-08

Searches for `deterministic Minami perturbation`,
`Minami deterministic eigenvalue gap algorithm 2026`, and `Minami
derandomization matrix` found no construction meeting this bound. Sobczyk's
April 2025 revision gives a deterministic full tridiagonal diagonalization in
nearly quadratic time; it does not provide the requested nearly linear
diagonal perturbation. The workshop retains Problem 3.2 in its August 2026
update. The normalization and a bounded perturbation are stated explicitly
here, making the scale of its gap guarantee unambiguous.

## Audit update — 2026-09-10

Rechecked [workshop version 3](https://arxiv.org/html/2602.05394v3), Problem 3.2. Searches for deterministic Minami-type separation and nearly linear tridiagonal perturbation constructions found no solution of the simultaneous separation and runtime requirements.
