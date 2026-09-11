# FR-11 — The minimum number of quadratic measurements for generalized phase retrieval

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging
**Importance:** interesting to the community
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** Exact thresholds across all dimensions require algebraic and topological analysis beyond known families; they guide quadratic matrix-measurement design.

<!-- colbrook-frames -->
## Reviewed submission - 2026-09-11

Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge.

The construction theorem and its proof give twelve explicit integral symmetric $7\times7$ matrices, with maximum absolute entry 144, that recover every real signal including zero up to sign. Thus $m_{\mathbb R}(7)\le12$ in the unrestricted self-adjoint model. No matching lower bound or all-dimension/all-field formula is established. The manuscript also proves quantitative separation and exact-arithmetic decoding; floating-point decoder tests are finite diagnostics, with a separately documented scaling correction.

See the [manuscript](../../references/colbrook-frames-2026-09-11/manuscripts/twelve_measurements.pdf), [independent agent review](../../references/colbrook-frames-2026-09-11/verification/reviews/FR-11-review.md), and [reproducible submission record](../../references/colbrook-frames-2026-09-11/README.md). Independent agent review is not external human peer review or formal proof-assistant certification. Original problem, ratings and historical audits are retained below.
<!-- /colbrook-frames -->

## Problem statement

Fix a field $\mathbb F\in\{\mathbb R,\mathbb C\}$ and an integer $d\ge2$.
For self-adjoint matrices $A_1,\ldots,A_m\in\mathbb F^{d\times d}$ define
$$
\Phi_A(x)=(x^*A_1x,\ldots,x^*A_mx)\in\mathbb R^m.
$$
Call the family phase retrievable if, for every $x,y\in\mathbb F^d$,
$$
\Phi_A(x)=\Phi_A(y)
\quad\Longrightarrow\quad
x=cy\text{ for some }c\in\mathbb F\text{ with }|c|=1.
$$
Let $m_{\mathbb F}(d)$ be the smallest $m$ for which such a family exists.
Determine $m_{\mathbb F}(d)$ exactly for all $d\ge2$ and both fields.
The matrices may be indefinite and have any rank. Recovery must hold for every signal, including zero. In the real case the ambiguity is only sign. The source's real and complex versions are grouped as one problem here.

## Relevance and ratings

This is the sharp measurement-design problem for recovering a rank-one Gram matrix from linear matrix measurements. Allowing arbitrary self-adjoint measurement matrices distinguishes it from the rank-one random-frame question FR-05. Exact thresholds in all dimensions involve substantial algebraic and topological obstructions.

## References

- Z. Xu, *Signal recovery on algebraic varieties using linear samples*, Acta Math. Sinica (English Series) 42 (2026), 740–754 ([journal](https://doi.org/10.1007/s10114-026-5299-y)); [arXiv:2506.17572v2](https://arxiv.org/pdf/2506.17572v2), §4, Problems 4.1 and 4.3; Theorems 4.3 and 4.8 give exact values in some dimensions.
- Y. Wang and Z. Xu, *Generalized phase retrieval: Measurement number, matrix recovery and beyond*, Appl. Comput. Harmon. Anal. 47 (2019), 423–446 ([primary manuscript](https://arxiv.org/abs/1605.08034); [journal](https://doi.org/10.1016/j.acha.2017.09.003)).

## Status check — 2026-09-10

Xu explicitly retains both full threshold questions. Bounds and exact dimensional families do not determine either entire function. Searches for generalized phase retrieval, minimum measurement number, and 2025–2026 found no complete solution. Xu's August 2026 [almost-everywhere result](https://arxiv.org/abs/2608.15003) concerns generic-signal recovery with rank-one measurements, not the all-signals requirement here. This distinction was checked in the new paper's stated theorem.

**Independent audit:** Independently rechecked Xu Problems 4.1 and 4.3 and the definitions preceding them. Theorems 4.3 and 4.8 settle dimensional families inside the displayed target, so the appropriate label is Partially resolved. Later generalized-phase-retrieval searches found no all-dimension threshold formula.
