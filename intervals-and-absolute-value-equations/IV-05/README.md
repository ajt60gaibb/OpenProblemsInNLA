# IV-05 — Exact solution hulls for inverse M-matrix intervals

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved
**Last checked:** 2026-09-11

**Rating rationale:** A polynomial hull algorithm would need to exploit the inverse-M promise beyond the known endpoint reductions, warranting challenging. Its direct impact is on a specialist class of verified linear-system computations.

**Area:** verified linear systems; interval complexity  

<!-- colbrook-intervals -->
## Independently reviewed resolution - 2026-09-11

**Affirmative algorithmic resolution.** Theorem 3 and Sections 3-5 give the exact coordinatewise solution hull using $2n$ rational LPs, each with $n$ variables and $2n$ inequalities, in polynomial binary input length. The construction uses precisely the inverse-M promise and arbitrary interval right-hand sides. Promise recognition is not needed; no solver for the general regular AV-03 problem is claimed.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. See the [complete manuscript](../../references/colbrook-intervals-2026-09-11/manuscripts/IV-05.pdf), [independent agent review](../../references/colbrook-intervals-2026-09-11/verification/reviews/IV-05-review.md) and [submission record](../../references/colbrook-intervals-2026-09-11/README.md). The source archive identifies the drafts as AI-generated; authorship is recorded at the submitter's request. This is agent verification, not external human peer review or formal proof-assistant certification.

The difficulty, importance and rating rationale below are historical assessments of the original open target. The original statement and dated audits are preserved.
<!-- /colbrook-intervals -->

## Problem statement

For arbitrary $n\ge1$, the input consists of rational matrices $L\le U$ and rational vectors $l\le u$, with entrywise inequalities. Let

$$
\mathcal A=\{A\in\mathbb R^{n\times n}:L\le A\le U\},\qquad
\mathcal b=\{b\in\mathbb R^n:l\le b\le u\}.
$$

Assume as a promise that every $A\in\mathcal A$ is an inverse M-matrix: $A^{-1}$ has nonpositive off-diagonal entries and is a nonsingular M-matrix. Here a nonsingular M-matrix means an invertible real matrix with nonpositive off-diagonal entries and entrywise nonnegative inverse. The entries of $A$ and $b$ vary independently.

Is there a deterministic algorithm that returns the exact rational endpoints of

$$
\prod_{i=1}^n
\left[\min_{A\in\mathcal A,\ b\in\mathcal b}(A^{-1}b)_i,
      \max_{A\in\mathcal A,\ b\in\mathcal b}(A^{-1}b)_i\right]
$$

in time polynomial in the binary input length? Behavior outside the promise is unrestricted, and checking the promise is not part of the requested algorithm. This is the precise bit-complexity formulation of the source's efficient interval-system solution-hull question.

The promise makes the solution set nonempty and compact. The aim is its smallest coordinatewise enclosure. Computing the interval hull of $A^{-1}$ separately is already easier in this matrix class; multiplying that enclosure by $\mathcal b$ need not capture the dependence among entries of the inverse.

## References

Milan Hladík, [*An overview of polynomially computable characteristics of special interval matrices*](https://doi.org/10.1007/978-3-030-31041-7_16), in *Beyond Traditional Probabilistic Data Processing Techniques*, Springer (2020), 295–310; [arXiv:1711.08732v1](https://arxiv.org/pdf/1711.08732), §9, p. 11, question immediately before Theorem 25. Theorem 24 concerns the different inverse-matrix hull; Theorem 25 specifies the right-hand-side vertices attaining each endpoint.

## Status check

On 2026-09-10, searches for inverse M-matrix interval systems, exact solution hull, polynomial/efficient computation, and 2025/2026 found no resolution. The author's publication list through 2026 and Garloff–Al-Saafin–Adm's [2021 interval-property paper](https://reliable-computing.org/reliable-computing-28-pp-056-070.pdf), §4, were checked. The latter addresses recognizing the matrix class, not this promised hull computation. The explicit openness statement remains historical.

## Independent audit — 2026-09-10

The full Hladík preprint, §9, asks the efficient hull question immediately before Theorem 25. That theorem fixes the optimizing right-hand-side vertices but leaves the matrix optimization unresolved; it is not a polynomial algorithm or a solved subclass of this target. The 2021 interval-property paper addresses recognition instead. Later searches specific to inverse M-matrix solution hulls found no resolution; the explicit open-status evidence remains historical.
