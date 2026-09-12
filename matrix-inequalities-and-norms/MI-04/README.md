# MI-04 — A universal block-norm characterization of essentially Hermitian matrices

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** The universal converse needs new control of positive block completions; its immediate impact is a specific numerical-range characterization.

## Resolution — 2026-09-11

**Affirmative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

The universal positive-block operator-norm property holds exactly when the off-diagonal block is essentially Hermitian. The proof applies in every finite dimension without invertibility or distinct-singular-value assumptions.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-04-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

Let $`n\ge1`$ and $`X\in\mathbb C^{n\times n}`$. Suppose that for every pair of Hermitian $`A,B\in\mathbb C^{n\times n}`$ for which

```math
H=\begin{bmatrix}A&X\\X^*&B\end{bmatrix}\succeq0,
```

one has $`\|H\|_2\le\|A+B\|_2`$, where $`\|\cdot\|_2`$ is the operator norm. Must there exist a Hermitian $`K`$ and scalars $`\alpha,\beta\in\mathbb C`$ with $`X=\alpha K+\beta I_n`$?

Such an $`X`$ is called essentially Hermitian; equivalently its numerical range $`\{v^*Xv:\|v\|_2=1\}`$ lies in an affine line.

## Why it matters

The question characterizes exactly when off-diagonal coupling in a positive block matrix can always be ignored in a particular spectral-norm bound. It connects a numerical-range geometry condition to a universal norm estimate.

## References

1. J.-C. Bourin and E.-Y. Lee, *Eigenvalue inequalities for positive block matrices with the inradius of the numerical range*, arXiv:2111.15180v1 (30 November 2021), Conjecture 3.3, Theorem 3.2, and Proposition 3.4. [Primary text](https://arxiv.org/html/2111.15180).
2. T. Hayashi, *On a norm inequality for a positive block-matrix*, Linear Algebra and its Applications 566 (2019), 86–97, Theorem 2.5. [Preprint](https://arxiv.org/abs/1808.00181), [DOI](https://doi.org/10.1016/j.laa.2018.12.027).

## Status check — 2026-09-10

The latest arXiv version of reference 1 remains v1. Hayashi proves normality under additional invertibility and distinct-singular-value assumptions, not the stated conclusion in full generality. A Frobenius-norm variant characterizes normality and is already proved. Searches included `Bourin essentially Hermitian conjecture`, `universal positive block matrix norm Hayashi conjecture`, and `essentially Hermitian conjecture proof 2025 2026`. No later resolution of Conjecture 3.3 was located. A 2025 result on decomposable numerical ranges settles a different conjecture.

**Audit update (2026-09-10):** Rechecked Bourin–Lee Conjecture 3.3 and searched for subsequent essentially-Hermitian characterizations. The Frobenius-norm theorem has a different norm and conclusion; no resolution of the operator-norm converse was located. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
