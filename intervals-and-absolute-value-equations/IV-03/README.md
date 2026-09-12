# IV-03 — Polynomial-size vertex test for inverse M-matrix intervals

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved
**Last checked:** 2026-09-11

**Rating rationale:** Replacing an exponential interval test by a quadratic vertex family is challenging; verified inverse-positivity has specialist importance in interval matrix analysis.

**Area:** interval linear algebra; structured matrices  

<!-- colbrook-intervals -->
## Independently reviewed resolution - 2026-09-11

**Affirmative resolution.** Theorem 1 proves that every interval member is inverse-M if and only if the $`n^2`$ vertices $`C-D_iRD_j`$ are inverse-M. These are contained in the displayed two-sign family, so the original $`2n^2`$ equivalence follows. The proof covers all real endpoints, every dimension, zero widths, zero entries and reducible matrices without assuming regularity.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. See the [complete manuscript](../../references/colbrook-intervals-2026-09-11/manuscripts/IV-03.pdf), [independent agent review](../../references/colbrook-intervals-2026-09-11/verification/reviews/IV-03-review.md) and [submission record](../../references/colbrook-intervals-2026-09-11/README.md). The source archive identifies the drafts as AI-generated; authorship is recorded at the submitter's request. This is agent verification, not external human peer review or formal proof-assistant certification.

The difficulty, importance and rating rationale below are historical assessments of the original open target. The original statement and dated audits are preserved.
<!-- /colbrook-intervals -->

## Problem statement

A real square matrix $`M`$ is a nonsingular M-matrix if its off-diagonal entries are nonpositive, $`M`$ is invertible, and $`M^{-1}`$ is entrywise nonnegative. An inverse M-matrix is the inverse of such a matrix.

For every $`n\ge1`$, let $`L,U\in\mathbb R^{n\times n}`$ satisfy $`L\le U`$ entrywise, and set

```math
\mathcal A=\{A:L\le A\le U\},\qquad C=(L+U)/2,\qquad R=(U-L)/2.
```

For $`i=1,\ldots,n`$, let $`z^{(i)}`$ have entry $`-1`$ in position $`i`$ and entry $`1`$ elsewhere, and write $`D_i=\mathop{\mathrm{diag}}\nolimits(z^{(i)})`$.

Is the following equivalence true?

```math
\begin{gathered}
\bigl[\text{every }A\in\mathcal A\text{ is an inverse M-matrix}\bigr]
\\\Longleftrightarrow\\
\left[\begin{gathered}
C+sD_iRD_j\text{ is an inverse M-matrix}\\
\text{for every }i,j\in\{1,\ldots,n\}\text{ and }s\in\{-1,1\}
\end{gathered}\right].
\end{gathered}
```

All entries in the interval vary independently, and degenerate intervals are allowed. The proposed test uses at most $`2n^2`$ matrices; repeated test matrices are harmless. This would give a small exact certificate for a structured property needed in interval inversion and verified linear-system computation.

## References

Milan Hladík, [*An overview of polynomially computable characteristics of special interval matrices*](https://doi.org/10.1007/978-3-030-31041-7_16), in *Beyond Traditional Probabilistic Data Processing Techniques*, Springer (2020), pp. 295–310; [author preprint, arXiv:1711.08732v1](https://arxiv.org/pdf/1711.08732), §9, Conjecture 1, p. 11, with the vectors defined in Theorem 24.

Jürgen Garloff, Doaa Al-Saafin, and Mohammad Adm, [*Further Matrix Classes Possessing the Interval Property*](https://reliable-computing.org/reliable-computing-28-pp-056-070.pdf), Reliable Computing **28** (2021), 56–70, p. 64, paragraph immediately before IP 4.4.

## Status check

The 2021 paper explicitly retains this conjecture while proving a different sufficient vertex family of size $`2^{n-1}`$. On 2026-09-10, searches combining the original title, inverse M-matrices, interval property, conjecture, and 2025/2026 found no resolution. Hladík's current publication list and the later interval-property paper were checked. This is a selected-source status check, not an exhaustive citation audit.

## Independent audit — 2026-09-10

The full Hladík preprint, §9, Conjecture 1, agrees with the displayed two-sign vertex family, including the definition of each $`z^{(i)}`$. Garloff–Al-Saafin–Adm, p. 64, expressly leaves that conjecture unresolved; its exponential family is a different test, not a resolution for a subclass here. Independent later searches for the exact conjecture and matrix class found no resolution.
