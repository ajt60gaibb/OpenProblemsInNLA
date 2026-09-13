# MI-16 — The maximum permanent on a positive-semidefinite unitary orbit

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Provenance:** explicit exact extremal problem; no conjectured optimizer is supplied  
**Status:** Solved
**Last checked:** 2026-09-12

**Historical rating rationale:** An exact formula for arbitrary spectra would resolve a longstanding permanent optimization barrier and inform prescribed-spectrum matrix optimization.

## Resolution — exact algebraic determination, 12 September 2026

**Solved by Sidney Holden**, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Submission and verified affiliation](../../references/holden-mi16-2026-09-12/README.md). [Proof PDF](solution.pdf) · [LaTeX source](solution.tex) · [Independent AI-agent audit: PASS](../../references/holden-mi16-2026-09-12/independent-review.md).

Theorem 2.1 and Sections 3–5 give an exact finite algebraic prescription for every nonnegative real spectrum in every order. A specialized critical-value elimination polynomial gives finitely many candidates. Explicit Schur-character sums compute a spectral moment at a proved finite order, which selects the maximum even when some real critical values are not Hermitian-feasible. The prescription has no remaining matrix optimization or unevaluated limit, and meets the original exact-value criterion below. For arbitrary real inputs it uses exact ordered-field arithmetic and comparisons; the reference programs accept rational inputs.

**Form of the answer:** this is not a compact general structural formula, an efficient arbitrary-order solver, or a classification of all general-spectrum optimizers. Those stronger goals are not claimed. Theorem 8.1 separately gives a two-candidate structural formula for one exceptional eigenvalue; Sections 9–10 prove the transition threshold and every equality case. The earlier rank-one expansion and equal-support reduction from [Holden's partial submission, PR #186](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/186), are retained and credited in the dossier. This submission adds the all-spectrum determination and sharper exceptional-spectrum results.

A separate Codex agent independently audited the complete argument and its correspondence with this unchanged target. This is informal AI-agent review, not external human peer review or formal verification. No Lean verification or historical-priority claim is made. Whether a structural formula is preferred for the historical problem is exposed for maintainer review; it is not silently added to this entry's completion criterion.

## Problem statement

For every integer $`n\ge1`$ and every real list $`\lambda=(\lambda_1,\ldots,\lambda_n)`$ with $`\lambda_i\ge0`$, determine the exact value of

```math
M_n(\lambda)=\max_{U\in\mathcal U_n}
\mathop{\mathrm{per}}\nolimits\!\left(U^*\mathop{\mathrm{diag}}\nolimits(\lambda_1,\ldots,\lambda_n)U\right),
\qquad \mathcal U_n=\{U\in\mathbb C^{n\times n}:U^*U=I_n\},
```

where $`\mathop{\mathrm{per}}\nolimits(C)=\sum_{\sigma\in S_n}\prod_{i=1}^n c_{i,\sigma(i)}`$ and $`S_n`$ is the permutation group. The permanent of these Hermitian positive-semidefinite matrices is real. Compactness ensures the maximum exists. A resolution should express its value from the prescribed eigenvalues for arbitrary order, rather than only bound the objective or restate its optimization definition.

## Relevance

The eigenvalues fix an entire unitary similarity class while the permanent varies within it. Determining its extreme value is a concrete optimization problem over matrices with a prescribed spectrum.

## References

1. F. Zhang, *An update on a few permanent conjectures*, Special Matrices 4 (2016), 305–316, passage headed “Marcus–Minc max-per-$`U`$ problem 1965.” [Primary text](https://arxiv.org/html/1608.02844v1); [journal](https://doi.org/10.1515/spma-2016-0030).
2. J. H. Drew and C. R. Johnson, *Counterexample to a conjecture of Mehta regarding permanental maximization*, Linear and Multilinear Algebra 25(3) (1989), 253–254, the counterexample. [DOI](https://doi.org/10.1080/03081088908817948).

## Status check — 2026-09-10

Zhang's latest arXiv record is v1 and explicitly lists the general maximization problem. Its statement and discussion of the equal-diagonal counterexample were inspected. The original 1989 full text was not retrieved; that counterexample's role was checked through Zhang's explicit account and bibliography. Searches used `maximum permanent unitary 2026`, `maximum permanent eigenvalues 2025 2026`, and `Marcus-Minc max-per-U problem`. No general spectral formula was located. The claim that an equal-diagonal representative always maximizes the permanent is false and is not imposed. The other catalog permanent entries concern inequalities between distinct matrix functions or products, not this exact orbit maximum.

**Audit update (2026-09-10):** Rechecked Zhang’s Marcus–Minc max-per-$`U`$ statement and searched for later exact spectral formulas. Equal-diagonal optimality remains an invalid shortcut; no all-spectrum determination was located. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
