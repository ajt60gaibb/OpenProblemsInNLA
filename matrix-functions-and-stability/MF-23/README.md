# MF-23 — Complete Crouzeix conjecture

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Matrix-valued polynomial functional calculus  
**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Solved
**Last checked:** 2026-10-08

**Rating rationale:** Historical ratings retained. The uniform bound must survive arbitrary matrix amplification, beyond the scalar functional calculus; it would give sharp bounds for block matrix functions and connect numerical-range estimates to dilation and similarity theory.

## Resolution — independently audited 8 October 2026

OpenAI's [mathematics catalog, family 325](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/CONTENTS.md) reports a proof of the sharp constant-two inequality for finite matrix-valued polynomials, and a stronger version for bounded operators on arbitrary complex Hilbert spaces. Two [independent informal AI-agent audits](../../reviews/2026-10-08-claimed-solutions/MF-23.md) read all 12 pages of the [direct proof manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/paper.pdf), checked its central positive-kernel and block-matrix arguments, and found no gap. Theorem 1.1 covers all base and coefficient sizes and point or line-segment numerical ranges. Its tensor-factor order differs from the block notation below only by a unitary flip. This establishes the original MF-23 target under the catalog's informal-audit rule. The stronger [Hilbert-space manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf) was not audited here. The problem ID, canonical path and statement are retained.

At immutable OpenAI revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, the project publishes a [Lean formalization scope record](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/325.md). Its [finite-matrix proof source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/DirectCrouzeix/CompleteBound.lean) declares `OAI.DirectCrouzeix.complete_crouzeix : UniversalBound 2`. The [Comparator challenge](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DirectCrouzeix.lean) defines `UniversalBound` with arbitrary positive matrix sizes, degree and complex coefficients, using the Euclidean operator norm and the supremum over the numerical range. The [formalization catalog](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/formalization.yaml) maps the declaration to this challenge, and its [Comparator configuration](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DirectCrouzeix.json) permits only Lean's standard foundational axioms.

**Lean evidence check, 8 October 2026:** the pinned proof source declares the exact `UniversalBound 2` target. The [review](../../reviews/2026-10-08-claimed-solutions/MF-23.md) compared its definitions with the Comparator challenge and scanned the direct proof modules for placeholders and bypasses. The repository publishes a pinned toolchain and dependencies, but no dated successful kernel build or Comparator log and no transitive axiom report were found for the cited revision. This therefore remains **Solved**, not `Lean verified`, under the catalog's [formal evidence criteria](../../CONTRIBUTING.md#lean-verification). No external human peer review or local Lean rerun is asserted.

## Context and notation

All matrices are complex, and all norms are Euclidean operator norms. For
$`A\in\mathbb C^{n\times n}`$ define

```math
W(A)=\{x^*Ax:x\in\mathbb C^n,\ x^*x=1\}.
```

If $`F(z)=[f_{ij}(z)]_{i,j=1}^m`$ has polynomial entries, let
$`F(A)=[f_{ij}(A)]_{i,j=1}^m`$, an $`mn\times mn`$ block matrix.

## Problem statement

Prove or disprove that, for every $`n,m\geq1`$, every
$`A\in\mathbb C^{n\times n}`$ and every matrix polynomial
$`F\in\mathbb C^{m\times m}[z]`$,

```math
\|F(A)\|_2\leq 2\max_{z\in W(A)}\|F(z)\|_2.
```

This is the complete, rather than scalar, numerical-range spectral-set question.
It controls simultaneous polynomial functions and hence block approximation
errors with one constant independent of matrix and block sizes.

## References

- Michel Crouzeix, [*Numerical range and functional calculus in Hilbert space*](https://doi.org/10.1016/j.jfa.2006.10.013), *Journal of Functional Analysis* **244**(2), 668–690 (2007). Original source for the complete conjecture, as explicitly attributed in the next source.
- Per Åhag, Rafał Czyż and Jani Virtanen, [*Square Functions, Complete Crouzeix Conjecture in Dimension Three, and the Clouâtre–Ostermann–Ransford conjecture*, arXiv:2608.27346v3](https://arxiv.org/html/2608.27346v3), **9 September 2026**, Introduction, equation **(1.2)** and **Theorem 1.1**. This current version states the exact target and explicitly distinguishes it from the scalar proofs. It claims the complete bound for $`n\leq3`$. Its counterexample reduction leaves only $`2\times2`$ matrix polynomials to check when $`n=4`$.
- Michel Crouzeix and César Palencia, [*The numerical range is a $`(1+\sqrt2)`$-spectral set*](https://doi.org/10.1137/17M1116672), *SIAM Journal on Matrix Analysis and Applications* **38**(2), 649–655 (2017). The complete universal upper bound is $`1+\sqrt2`$.

## Earlier scope and status check (11 September 2026)

The target is source-stated, not an editorial extension of the scalar conjecture.
The August 2026 scalar proof claims by Jin and by Lorist–Schwenninger do not settle
it: the September 9 primary manuscript explicitly addresses this distinction.
The $`n=3`$ result was then a recent preprint claim; the full displayed target remained
unresolved even if that claim was accepted. Searches through 11 September 2026 for
complete Crouzeix proofs, matrix-valued Crouzeix inequalities and later versions
found no full solution. The version was inspected as both HTML and PDF; the
inequality is on PDF page 2, immediately before Theorem 1.1.
