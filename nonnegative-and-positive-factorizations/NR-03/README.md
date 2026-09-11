# NR-03 — Full nonnegative rank of the quadratic correlation matrix

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because full nonnegative rank is much sharper than available exponential lower bounds for this family; broad importance concerns communication complexity and limitations of linear programming formulations.  
**Status:** Partially resolved  
**Area:** exact NMF and lower bounds for optimization formulations  
**Last checked:** 2026-09-11  

<!-- colbrook-factorization -->
## Partial result — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the stated partial scope.**

The fixed three-bit quadratic correlation matrix has nonnegative rank exactly eight. Its ordinary-rank-seven parity null vector constrains both factors in a hypothetical seven-term factorization; nine distinguished entries then exclude such a factorization.

**Remaining question:** The full prescribed-completion conjecture for every $n\ge4$ remains unresolved. The parity restriction is proved only for a hypothetical factorization whose inner dimension equals ordinary rank; it is not imposed on arbitrary wider factorizations. The ratings assess that surviving question.

**Primary reference:** [complete authored PDF](../../references/colbrook-factorization-2026-09-11/manuscripts/NR-03_n3_exact_rank.pdf), [standalone TeX](../../references/colbrook-factorization-2026-09-11/manuscripts/NR-03_n3_exact_rank.tex), **Theorem 1 and Lemma 2**. [Independent proof review](../../references/colbrook-factorization-2026-09-11/verification/reviews/NR-03-review.md) · [Authorship and submission record](../../references/colbrook-factorization-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-factorization -->

## Context and notation

All factorizations are over the real numbers. For
$X\in\mathbb R_{\ge0}^{m\times n}$, define

$$
\operatorname{rank}_+(X)=\min\{r\ge0:X=WH,\quad
W\in\mathbb R_{\ge0}^{m\times r},\ H\in\mathbb R_{\ge0}^{r\times n}\}.
$$

## Problem statement

For each integer $n\ge3$, let $C_n$ be the $2^n\times2^n$ matrix indexed by
$a,b\in\{0,1\}^n$ and defined by

$$
C_n(a,b)=(1-a^{\mathsf T}b)^2.
$$

### Question

Is $\operatorname{rank}_+(C_n)=2^n$ for every $n\ge3$?
All entries, including those for $a^{\mathsf T}b>1$, are fixed by this formula.

The matrix has ordinary rank $1+n(n+1)/2$ and is a submatrix of a slack matrix
of the correlation polytope formed from valid, possibly redundant inequalities.
The conjecture therefore asks for a large
separation between ordinary and nonnegative matrix rank with consequences for
linear programming representations.

## References

Vandaele, Gillis, Glineur, and Tuyttens,
[*Heuristics for Exact Nonnegative Matrix Factorization*](https://arxiv.org/html/1411.7245),
§6.4, Conjecture 4. Gillis,
[*Nonnegative Matrix Factorization*](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf),
§3.7, p. 96, using the name $U_n$ for this fixed matrix.

## Status check — 2026-09-10

Rechecked [Baeckelant et al. v2, §6.7 and Appendix A.4](https://arxiv.org/html/2605.14058v2) and [Sergeev’s July 2026 paper](https://arxiv.org/abs/2607.27014), and searched for a full-rank resolution. The former retains the prescribed-completion conjecture, including the unresolved n=3 case. Sergeev treats a partial unique-disjointness matrix whose remaining entries may vary; this does not determine the rank of the fixed matrix here. No full resolution was located.

