# AC-12 — Realizing every sign-matrix permanent with negative entries confined on or above the diagonal

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because equality of the full permanent ranges requires a uniform value-preserving construction or an obstruction; specialist importance concerns structural realization of discrete matrix invariants.  
**Status:** Solved
**Last checked:** 2026-11-27

## Resolution — 2026-11-27

**Solved negatively.** Theorem 1.1 of
[*An order-eleven counterexample to triangular realization of sign matrix
permanents*](https://hexagonmath.org/2611.00424v1) constructs a sign
matrix of order eleven with permanent $`2{,}029{,}568`$. It proves that no
order-eleven sign matrix with all entries below the diagonal equal to
$`+1`$ has that permanent. The paper is signed OpenBMB and was deposited
by Weiming Zhang.

The [independent informal Codex audit](solution.md) checked the suffix
recurrence and pruning argument, reproduced all 34,099 terminal cofactor
profiles and verified the witness and terminal exclusions separately.

<!-- colbrook-arithmetic -->
## Independently reviewed finite cases - 2026-09-11

Exact restricted-family witnesses and exhaustive unrestricted-range inclusion checks establish equality of the signed permanent ranges for every order $`1\leq n\leq10`$. Entries below the diagonal are $`+1`$, and negative diagonal entries are allowed, exactly as in the original target. Both witness membership and exhaustive inclusion are checked. At the September review, the all-orders assertion remained unresolved.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](../../references/colbrook-arithmetic-2026-09-11/manuscripts/AC-11-12.pdf), [independent review](../../references/colbrook-arithmetic-2026-09-11/verification/reviews/AC-11-12-review.md), and [submission record](../../references/colbrook-arithmetic-2026-09-11/README.md). AI assistance is disclosed. Agent verification is not external human peer review or formal certification; no novelty or priority claim is made.

The [fresh certificate checks](../../references/colbrook-arithmetic-2026-09-11/verification/fresh/README.md) complement the analytic review. The canonical statement and its historical ratings follow below.

<!-- /colbrook-arithmetic -->

## Problem statement

For each integer $`n\ge1`$, let

```math
\Omega_n=\{-1,1\}^{n\times n},\qquad
\mathcal U_n=\{B\in\Omega_n:b_{ij}=1\text{ whenever }i>j\}.
```

Define $`\mathop{\mathrm{per}}\nolimits A=\sum_{\sigma\in S_n}\prod_{i=1}^n a_{i,\sigma(i)}`$.
Does every $`A\in\Omega_n`$ admit some $`B\in\mathcal U_n`$ with

```math
\mathop{\mathrm{per}}\nolimits B=\mathop{\mathrm{per}}\nolimits A?
```

Equivalently, do $`\Omega_n`$ and $`\mathcal U_n`$ have identical permanent ranges for every $`n`$? Entries below the diagonal are $`+1`$, not zero. Negative entries are allowed on the diagonal.

## Relevance and ratings

A positive answer would reduce exact value realization to a smaller, explicitly structured family of matrices. The question connects matrix structure and the combinatorial complexity of the permanent; it does not ask for an efficient permanent-evaluation algorithm. The main significance is to specialists, and a uniform structural argument or counterexample is required.

## References

- D. Ingram and A. Razborov, *On the range of the permanent of $`(\pm1)`$-matrices*, Linear Algebra Appl. 743 (2026), 271–285 ([journal](https://doi.org/10.1016/j.laa.2026.04.027)); [arXiv:2507.09433v1](https://arxiv.org/html/2507.09433v1), §6, Problem 4 and the paragraph defining the restricted family.
- Z. Hunter, M. Kwan and L. Sauermann, *Exponential anticoncentration of the permanent* (2025), §1.2, Corollary 1.3 ([primary paper](https://arxiv.org/abs/2509.22577)).

## Status check — 2026-09-10

Checked [Ingram–Razborov, §6, Problem 4](https://arxiv.org/html/2507.09433v1), including the preceding definition: negative entries may occur on or above the diagonal. The displayed target matches that question. Exact-title and upper-triangular permanent-range searches found no general resolution. [Hunter–Kwan–Sauermann, Corollary 1.3](https://arxiv.org/abs/2509.22577), settles exponential growth of the unrestricted range, not equality with this restricted family; rank-dependent maximum results also leave exact ranges undetermined.
