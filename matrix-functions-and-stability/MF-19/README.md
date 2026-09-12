# MF-19 — Decidability of zero hitting by rational matrix powers

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Unconditional decidability in unrestricted dimension is an extreme longstanding barrier; reachability, recurrences and exact linear dynamics give broad significance.

## Problem statement

Does there exist a single algorithm which, given a positive integer $`d`$, a matrix $`A\in\mathbb Q^{d\times d}`$, and vectors $`u,v\in\mathbb Q^d`$, always halts and correctly decides whether

```math
u^{T}A^kv=0\qquad\text{for some integer }k\ge0?
```

All rational inputs are represented exactly, for example by binary integers for numerators and nonzero denominators. There is no a priori bound on $`d`$, on the entries, or on the hitting time $`k`$. The output sought is a yes/no answer; numerical near-zero detection does not suffice.

This is the Skolem problem in its matrix-power form. Equivalently, one is given rational coefficients and initial values for a finite-order scalar linear recurrence and asks whether one of its terms vanishes. These equivalent formulations form one catalog entry.

The matrix formulation asks whether a discrete linear system reaches a specified hyperplane. It is directly relevant to exact observability, reachability, and verification of linear dynamics, and exposes a fundamental limit of computations with powers of matrices.

## References

1. P. Bacik, T. Karimov, F. Luca, J. Nieuwveld, J. Ouaknine, D. Purser and J. Worrell, *A survey of the Skolem and Positivity Problems for linear recurrence sequences*, submitted (2026), §1, Problem 2, and the discussion of linear dynamical systems; §5. [Author-hosted PDF](https://people.mpi-sws.org/~joel/publications/skolem_and_positivity_survey26.pdf).
2. F. Luca, J. Ouaknine and J. Worrell, *Conjectural Decidability of the Skolem Problem*, arXiv:2607.15510v1 (2026), §1. [Full preprint](https://arxiv.org/pdf/2607.15510).

Status check (2026-09-10): the 2026 survey still poses the general problem. The July 16 preprint proves conditional decidability under a strengthened prime-gap conjecture and an unconditional density-one universal Skolem-set result; it does not supply an unconditional algorithm on all inputs. Its current arXiv record is v1. Searches for “Skolem Problem decidability solution 2026”, including September developments, found special-family and positive-characteristic results but no general rational-input resolution. This is a dated, bounded status check.

## Audit — 2026-09-10

Independently rechecked [Luca–Ouaknine–Worrell, §1](https://arxiv.org/pdf/2607.15510), its current v1 record, and the [2026 survey's author abstract](https://people.mpi-sws.org/~joel/publications/skolem_and_positivity_survey26abs.html). The order-at-most-four decidability result gives a substantive exact subclass (in particular, $`d\le4`$ here), justifying Partially resolved; conditional decidability and density-one sets do not settle unrestricted inputs. Later Skolem-decidability searches found no unconditional general resolution. Both ratings are retained.
