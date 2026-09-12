# TR-07 — Random column subsets of arbitrary fixed-sparsity matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Historical ratings for the original open target. Challenging because arbitrary support intersections defeat existing sparse-matrix estimates; community impact is understanding limits of sparse sketches and column selection.  
**Status:** Solved  
**Last checked:** 2026-09-12  

## Resolution: affirmative, 12 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation, New York, USA. [Official affiliation](https://www.simonsfoundation.org/people/sidney-holden/) verified 12 September 2026.

[Theorem 1.1 and Corollary 1.2](solution.pdf) of *Random column subsets of fixed-sparsity matrices: an unrestricted theorem* prove the full statement below. The finite exponential tail bound covers arbitrary signs, repeated columns and unrestricted support intersections. Setting the aspect-ratio lower bound to $`1/(2C)`$ yields the exact asymptotic target. No growing-sparsity rate is claimed.

A separate [independent Codex AI-agent audit](../../references/holden-tr07-2026-09-12/independent-review.md) returned PASS without mathematical corrections, satisfying the **Solved** policy. AI assistance was used for review and submission preparation; this is informal automated review, not human peer review or formal verification. No Lean verification was performed. [Proof source](solution.tex) · [Submission record](../../references/holden-tr07-2026-09-12/README.md).

Huang, Rudelson and Tikhomirov retain conjecture and prior-result credit. The original target and ID remain unchanged; the earlier checks below are historical.

## Problem statement

Fix an integer $`s\ge2`$ and $`C\ge1`$. Suppose $`r_k\le k`$, $`k/r_k\to C`$, and $`n_k/r_k\to\infty`$. For every deterministic sequence $`M_k\in\{-1,0,1\}^{k\times n_k}`$ with exactly $`s`$ nonzero entries per column, and a uniformly random $`r_k`$-element column set $`I_k`$, prove or disprove

```math
\forall\eta>0,\qquad
\Pr\{\sigma_{\min}((M_k)_{:I_k})>\eta\}\longrightarrow0.
```

Here $`\sigma_{\min}(B)=\inf_{\|x\|_2=1}\|Bx\|_2`$. There is no hypothesis controlling intersections of column supports.

## Reference

Han Huang, Mark Rudelson, and Konstantin Tikhomirov, [*Well-Invertible Column Subsets of Sparse Matrices Are Rare*](https://arxiv.org/html/2607.05384v2), §7, Conjecture 7.1; compare Theorem 1.3 for the additional structural hypothesis in the proved result.

## Status check

Searches included `"unrestricted deterministic sparse sketches" conjecture` and the exact paper title with `2026`. No subsequent resolution was located. The paper’s disproof of a particular SparseStack conjecture does not establish its own unrestricted deterministic conjecture.

## Audit — 2026-09-10

Rechecked [Huang–Rudelson–Tikhomirov, Theorem 1.3 and Conjecture 7.1](https://arxiv.org/html/2607.05384v2): a structural subclass is proved, while arbitrary deterministic supports remain conjectural. Title and sparse-subset follow-up searches found no full resolution. [Tikhomirov's later embedding paper](https://arxiv.org/html/2607.23017v1) studies random models and spectral-norm estimates, not all deterministic support patterns.
