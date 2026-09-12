# TR-03 — Sharp gap between volume sampling and the worst matrix with a prescribed spectrum

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because the adversarial eigenvector choice and optimal subset must be compared sharply; community impact is spectrum-sensitive Nyström and column selection.  
**Status:** Partially resolved  
**Last checked:** 2026-09-12  

## Partial resolution: the one-column case, 12 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation, New York, USA. [Official affiliation](https://www.simonsfoundation.org/people/sidney-holden/) verified 12 September 2026.

[Theorem 1 and Sections 2-3 of the note](../../references/holden-tr03-2026-09-12/one-column.pdf) prove $`x_1(\lambda)=y_1(\lambda)`$ and therefore $`R_{n,1}=1`$ for every $`n\ge3`$ and every positive spectrum. The proof preserves the original real orthogonal model and max-min quantifier order: a zero-diagonal orthogonal basis for a trace-zero symmetric matrix equalizes all one-column residuals.

A separate [independent Codex AI-agent review](../../references/holden-tr03-2026-09-12/independent-review.md) returned **PASS for this special case**. The joint dependence for $`2\le k\le n-2`$, $`n\ge4`$, remains unresolved; this is not a full solution. The elementary identity is recorded without a novelty or priority claim. The original target and ID are unchanged, and the historical checks below are retained. AI assistance was used for review and submission preparation; informal automated review is not external human peer review or formal verification. No Lean verification was performed. [Proof source](../../references/holden-tr03-2026-09-12/one-column.tex) · [Submission record](../../references/holden-tr03-2026-09-12/README.md).

## Problem statement

For $`n\ge3`$, $`1\le k\le n-2`$, and $`\lambda\in(0,\infty)^n`$, write $`K_V=V^T\mathop{\mathrm{diag}}\nolimits(\lambda)V`$, $`V\in O(n)`$, and define

```math
x_k(\lambda)=\max_{V\in O(n)}\min_{|I|=k}
\mathop{\mathrm{tr}}\nolimits\bigl(K_V-(K_V)_{:I}(K_V)_{II}^{-1}(K_V)_{I:}\bigr),
\quad
y_k(\lambda)=(k+1)\frac{e_{k+1}(\lambda)}{e_k(\lambda)},
```

where $`e_j(\lambda)=\sum_{|I|=j}\prod_{i\in I}\lambda_i`$. Determine, up to universal multiplicative constants, the dependence on $`n,k`$ of

```math
R_{n,k}=\sup_{\lambda\in(0,\infty)^n}\frac{y_k(\lambda)}{x_k(\lambda)}.
```

Here $`y_k`$ is the expected trace error when the selected subset has probability $`\det((K_V)_{II})/e_k(\lambda)`$. The question compares that expectation with optimal subset selection after an adversary chooses the eigenvectors. This order of quantifiers is essential. The endpoint $`R_{n,n-1}=1`$ is known and excluded. The displayed supremum is a concrete subquestion of the source’s request for spectrum-dependent tightness bounds; stronger bounds retaining the full spectrum would also be valuable.

## References

Amsel et al., [workshop report](https://arxiv.org/html/2602.05394v3), §4.2, Problem 4.7 and equations (15)–(16). Mark Fornace and Michael Lindsey, [*Column and Row Subset Selection Using Nuclear Scores: Algorithms and Theory for Nyström Approximation, CUR Decomposition, and Graph Laplacian Reduction*](https://arxiv.org/html/2407.01698v2), §4 and Appendix C, for determinantal sampling and the elementary-symmetric-polynomial formulas.

## Status check

Searches included `"minimax" "volume sampling" "2026"`, `"volume sampling" "worst" "spectrum" "2026"`, and `"volume sampling" "tightness" Fornace`. No matching sharp estimate for $`R_{n,k}`$ was located. Generic column-subset approximation guarantees do not by themselves settle this spectral minimax ratio.

## Audit — 2026-09-10

Rechecked [workshop Problem 4.7 and equations (15)–(16)](https://arxiv.org/html/2602.05394v3). They support the stated spectral-minimax subquestion. Volume-sampling, worst-spectrum, and tightness searches found no sharp joint estimate for the displayed ratio; generic subset guarantees leave its quantifier order unresolved.
