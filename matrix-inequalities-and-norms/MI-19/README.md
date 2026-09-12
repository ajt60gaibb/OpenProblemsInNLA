# MI-19 — A q-permanent inequality for subset-preserving permutations

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** Arbitrary subsets introduce inversion-order interactions absent for an initial segment; a solution would advance specialized block inequalities for generalized permanents.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

A real order-four PSD Gram matrix, $`q=7/8`$ and the interior singleton $`S=\{2\}`$ give full minus restricted $`q`$-permanent equal to $`-3235575/16384`$. Inversions are counted in the full original ordering. The strict counterexample also persists under sufficiently small positive diagonal perturbations.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-19-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

Let $`n\ge2`$, let $`A=(a_{ij})\in\mathbb C^{n\times n}`$ be Hermitian positive semidefinite, and let $`q\in[0,1]`$. Define

```math
\mathop{\mathrm{inv}}\nolimits(\sigma)=\#\{(i,j):i< j,\ \sigma(i)>\sigma(j)\},\qquad
P_q(A)=\sum_{\sigma\in S_n}q^{\mathop{\mathrm{inv}}\nolimits(\sigma)}
\prod_{i=1}^n a_{i,\sigma(i)},
```

with $`0^0=1`$. Is it true that every nonempty proper subset $`S\subset\{1,\ldots,n\}`$ satisfies

```math
P_q(A)\ge
\sum_{\substack{\sigma\in S_n\\ \sigma(S)=S}}
q^{\mathop{\mathrm{inv}}\nolimits(\sigma)}\prod_{i=1}^n a_{i,\sigma(i)}?
```

Here $`\sigma(S)=S`$ means setwise preservation. The inversion counts on the right are taken in the full ordering $`1,\ldots,n`$.

## Relevance and ratings

 This is a block comparison for a matrix function interpolating determinant and permanent. At $`q=1`$ it reduces to a known permanental block inequality. For general $`q`$, ordering matters: the right side must not be replaced by a product of q-permanents of the two principal submatrices for an arbitrary subset.

## References

- R. B. Bapat and A. K. Lal, *Inequalities for the q-permanent*, Linear Algebra and its Applications 197–198 (1994), 397–409 ([original paper](https://doi.org/10.1016/0024-3795(94)90497-9)).
- C. M. da Fonseca, *The $`\mu`$-permanent revisited* (2018), §5, Conjecture 3 and Theorem 5.1 ([primary manuscript](https://arxiv.org/pdf/1804.02231)).

## Status check — 2026-09-10

 Da Fonseca explicitly states this conjecture, attributes it to Bapat and Lal, and distinguishes proved initial-segment cases from arbitrary subsets. Searches for “q-permanent”, “mu-permanent”, “Lieb”, “subset”, “conjecture”, and “proof”, including 2025–2026, found no general resolution. The newest explicit formulation located is from 2018, so this entry has weaker recent status evidence than the other candidates. The separately refuted permanent-on-top conjecture is not included.

**Independent audit:** Independently rechecked da Fonseca Conjecture 3 and Theorem 5.1 and searched for later subset-preserving q-permanent results. Initial segments form a proved subfamily; arbitrary subsets remain unresolved in the sources located.
