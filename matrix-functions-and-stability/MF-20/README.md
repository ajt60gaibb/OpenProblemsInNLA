# MF-20 — Decidability of zero hitting by a matrix exponential

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Exact zero detection with arbitrary algebraic frequencies is an extreme decidability problem; certified continuous-system verification gives broad significance.

## Problem statement

Let $\overline{\mathbb Q}_{\mathbb R}$ denote the real algebraic numbers. Is there a single algorithm which, given $d\ge1$, $A\in\overline{\mathbb Q}_{\mathbb R}^{d\times d}$, $u,v\in\overline{\mathbb Q}_{\mathbb R}^d$, and an interval $I=[a,b]$ with rational $0\le a\le b$ or $I=[a,\infty)$ with rational $a\ge0$, always halts and decides whether

$$
u^T e^{tA}v=0\qquad\text{for some }t\in I?
$$

An algebraic real input is represented exactly by an integer polynomial and a rational isolating interval. The exponential is $e^{tA}=\sum_{j\ge0}(tA)^j/j!$. The witness time is a real number, not necessarily rational or algebraic. There is no diagonalizability assumption.

This is the continuous Skolem problem in matrix form. The equivalent scalar formulation asks whether the solution of a homogeneous linear differential equation with constant algebraic coefficients and algebraic initial data has a zero in $I$. Bounded and unbounded intervals are included in the same entry.

The problem is hyperplane reachability for a continuous linear dynamical system. Exact tangential contact can defeat simple sign-change detection, making the distinction between certified zero testing and numerical sampling important for matrix-exponential computations.

## References

1. V. Chonev, J. Ouaknine and J. Worrell, *On the Skolem Problem for Continuous Linear Dynamical Systems*, ICALP 2016, article 100, §1 (equivalent ODE and matrix formulations), §3, Theorem 7 (bounded case conditional on Schanuel's conjecture). [Full preprint, v3 (2016)](https://arxiv.org/pdf/1506.00695).
2. P. Bacik et al., *A survey of the Skolem and Positivity Problems for linear recurrence sequences* (2026), §9.1, continuous-time analogues. [Author-hosted PDF](https://people.mpi-sws.org/~joel/publications/skolem_and_positivity_survey26.pdf).

Status check (2026-09-10): the original full statement and current arXiv record were checked, along with the 2026 survey. The known Schanuel-conditional bounded result and partial frequency restrictions do not give an unconditional algorithm for all inputs. Searches for “continuous Skolem decidability 2025 2026” and the exact source title found no general resolution. Results on logical “Skolem functions” address a different problem. This is a bounded search report.

## Audit — 2026-09-10

Independently rechecked [Chonev–Ouaknine–Worrell, §1 and Theorem 7](https://arxiv.org/pdf/1506.00695). Added the exact unconditional subclass supporting Partially resolved: $d\le2$, $I=[0,\infty)$, proved in P. C. Bell, J.-C. Delvenne, R. M. Jungers and V. D. Blondel, [*The continuous Skolem-Pisot problem*](https://perso.uclouvain.be/vincent.blondel/publications/10BDJ.pdf), *Theoretical Computer Science* 411 (2010), 3625–3634, Theorem 10. The Schanuel-conditional result and reductions to a bounded problem are separate evidence of progress. The [2026 survey's author abstract](https://people.mpi-sws.org/~joel/publications/skolem_and_positivity_survey26abs.html) and targeted later searches yielded no unconditional general resolution. Both ratings are retained.
