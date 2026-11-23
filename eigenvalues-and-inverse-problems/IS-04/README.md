# IS-04 — A condition number of two for a sign matrix in every dimension

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solution claimed  
**Last checked:** 2026-11-23  

## Affirmative resolution claimed — 23 November 2026

Theorem 1 (p. 1) of *On the condition number of sign matrices*, submitted by Matias Andia, gives a real sign matrix with spectral condition number at most two in every positive dimension. The bound is strict outside order three, where the minimum equals two. Thus the supremum in IS-04 is two and is attained only at order three. The construction uses no symmetry or circulant assumption on the resulting matrix. GPT-6.2 Pro discovered the proof autonomously. AI wrote most of the manuscript, which Andia is reviewing and editing. [Paper](https://github.com/matias-ma/ai-math/blob/466673c69a4e074757a1f382283ef1b985e291e7/sign_matrix_condition_two/paper.pdf) · [Solution and reproduction instructions](https://github.com/matias-ma/ai-math/tree/main/sign_matrix_condition_two).

## Lean proof and verification evidence

The submission includes an external Lean 4.20.0 proof with Mathlib v4.20.0. `SignCond.verifiedMain` proves the equivalent Gram-matrix formulation of Theorem 1. For each positive order it supplies a sign matrix and a positive scale with $`tI\preceq AA^\top\preceq4tI`$, with a strict upper window available for the same matrix outside order three. At order three every admissible nonnegative condition-number bound is at least two. The eigenvalues of the Gram matrix are the squared singular values, giving the stated condition numbers and supremum. [Pinned final theorem](https://github.com/matias-ma/ai-math/blob/466673c69a4e074757a1f382283ef1b985e291e7/sign_matrix_condition_two/lean/Verified.lean).

The finite proposition is discharged by `SignCond.verifiedFinite`, including the Fourier bounds for all 9,983 sequence lengths. The submitter’s 23 November kernel audit reports only `propext`, `Classical.choice`, and `Quot.sound` for both declarations. From `sign_matrix_condition_two/lean` at the pinned revision, run `lake exe cache get` followed by `python3 verify_finite.py` for the full certificate replay and axiom report. Independent catalog review is pending. [Submitter’s axiom log](../../references/andia-is04-2026-11-23/axioms.txt).

<!-- colbrook-round3 -->
## Independently reviewed partial result - 2026-09-11

Theorem 1 constructs explicit real sign matrices of order $`p^2`$ for every odd prime $`p\geq13`$, with condition number at most $`(p+2+3\sqrt p)/(p-2-3\sqrt p)`$. For primes $`p\geq361`$ this is at most $`210/151<\sqrt2`$. This answers the cited paper\'s separate Problem 13, but does not prove the repository\'s bound in every dimension.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](../../references/colbrook-round3-2026-09-11/manuscripts/IS-04.pdf), [independent proof review](../../references/colbrook-round3-2026-09-11/verification/reviews/IS-04-review.md), and [submission record](../../references/colbrook-round3-2026-09-11/README.md). The supplied manuscripts and code disclose AI generation. Agent review is not external human peer review or formal certification; no novelty or priority claim is made.

<!-- /colbrook-round3 -->

**Rating rationale:** Historical assessment of the original problem. Challenging reflects a sharp universal constant whose remaining obstruction is a large finite set of dimensions; community impact is the construction of well-conditioned sign matrices.

## Problem statement

For $`n\geq1`$, define

```math
h(n)=\min_{A\in\{-1,1\}^{n\times n}}\kappa_2(A),\qquad
\kappa_2(A)=\frac{\sigma_{\max}(A)}{\sigma_{\min}(A)},
```

with $`\kappa_2(A)=+\infty`$ for singular $`A`$. Prove or disprove

```math
\sup_{n\geq1}h(n)=2.
```

Since $`h(3)=2`$, the claim to prove is the upper bound in every dimension.
No symmetry or circulant structure is imposed. The target refines the known
existence of uniformly well-conditioned sign matrices, which is useful for
constructing approximately isometric linear maps and well-conditioned bases.

## References

Alexeev, Jasper, and Mixon,
[*Asymptotically optimal approximate Hadamard matrices*](https://arxiv.org/html/2511.14653v1),
§6, Problem 12. Dong and Rudelson,
[*Approximately Hadamard matrices and Riesz bases in random frames*](https://arxiv.org/abs/2207.07523),
introduction; *IMRN* (2024), 2044–2065.

## Earlier status check — 2026-09-08

Searches for `approximate Hadamard sup 2 conjecture`,
`2511.14653 2026 condition number`, and `approximate Hadamard supremum`
found no proof of the sharp constant. The fact that $`h(n)\to1`$ is already
known and is not the problem counted here.

## Audit update — 2026-09-10

Rechecked [Alexeev–Jasper–Mixon](https://arxiv.org/html/2511.14653v1), §6, Problem 12. Their theorem $`h(n)\to1`$ implies the requested upper bound for every sufficiently large dimension, leaving finitely many dimensions unresolved; this is substantive partial resolution of the displayed universal statement. The numerical cutoff quoted there assumes the Hadamard conjecture and is not an unconditional completion. Supremum-two searches found no later full proof.
