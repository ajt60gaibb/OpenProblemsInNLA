# MI-08 — Minimum number of orthogonal conjugations for diagonal pinching

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** An exact all-dimension optimum imposes rigid real orthogonality constraints beyond a general upper bound; it would clarify matrix averaging and majorization decompositions.

## Partial result — 2026-09-11

**Partial result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS for the stated partial result.**

The fixed and adaptive orthogonal pinching lengths both equal the least row count $`h(d)`$ of a sign matrix $`H`$ with $`H^TH=h(d)I_d`$. In particular, the exact length is 12 for $`9\le d\le12`$.

**Still open:** The general value of $`h(d)`$ is undetermined; the all-dimension optimization remains open and includes Hadamard-order existence questions. The ratings apply to this surviving question.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-08-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For each integer $`d\ge1`$, define $`\Delta(X)=\mathop{\mathrm{diag}}\nolimits(x_{11},\ldots,x_{dd})`$ for $`X=(x_{ij})\in\mathbb R^{d\times d}`$. Determine the integer

```math
\varphi(d)=\min\left\{q\ge1:\ \exists U_1,\ldots,U_q\in O(d)\ \forall X\in\mathbb R^{d\times d},\quad
\Delta(X)=\frac1q\sum_{i=1}^qU_iXU_i^T\right\},
```

where $`O(d)=\{U\in\mathbb R^{d\times d}:U^TU=I_d\}`$. The same list of orthogonal matrices must work for every $`X`$. The minimum is finite: $`q=2^{\lceil\log_2d\rceil}`$ is always possible.

## Why it matters

Diagonal extraction is a basic matrix operation. Expressing it by the shortest average of orthogonal similarities gives an exact decomposition complexity and sharpens real versions of majorization-based norm estimates.

## References

1. J.-C. Bourin and E.-Y. Lee, *Averages over matrix unitary orbits and spectral order*, arXiv:2606.15624v2 (18 June 2026), Lemma 4.1 and Question 4.8. [Primary text](https://arxiv.org/html/2606.15624).
2. R. Bhatia, *Pinching, trimming, truncating, and averaging of matrices*, American Mathematical Monthly 107(7) (2000), 602–608, equation (2), for the complex unitary counterpart cited in reference 1. [DOI](https://doi.org/10.2307/2589115).

## Status check — 2026-09-10

The latest source is v2 and explicitly asks for the smallest length. Searches included `orthogonal pinching minimum phi Bourin Lee`, `Averages over matrix unitary orbits spectral order 2026`, and `diagonal pinching orthogonal matrices minimum`. No general determination was located. The adjacent Question 4.9 reverses the quantifier order by allowing the matrices to depend on $`X`$; it is not counted separately here. This is an exact optimization question rather than a conjectured closed formula.

**Audit update (2026-09-10):** Rechecked Question 4.8 in the current Bourin–Lee text and searched for minimal orthogonal pinching averages. The question remains explicit; allowing the conjugations to depend on $`X`$ is the different Question 4.9. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
