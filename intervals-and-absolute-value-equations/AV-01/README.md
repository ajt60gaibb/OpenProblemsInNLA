# AV-01 — Recognizing the maximum finite number of solutions

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved
**Area:** complexity of piecewise linear systems  
**Last checked:** 2026-09-11

**Rating rationale:** Challenging reflects a complexity classification for recognizing an exponential finite solution count; specialist impact concerns the solution geometry of absolute value equations.

<!-- colbrook-intervals -->
## Independently reviewed resolution - 2026-09-11

**Affirmative complexity classification.** Theorem 1 and the algorithm in Section 4 prove polynomial-time recognition of exactly $2^n$ distinct solutions to $Ax+|x|=b$ using $n+1$ rational LP feasibility tests. The result uses rational binary input, has no regularity or finiteness promise, and rejects infinite solution sets. It classifies the displayed decision problem in $\mathsf P$.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. See the [complete manuscript](../../references/colbrook-intervals-2026-09-11/manuscripts/AV-01.pdf), [independent agent review](../../references/colbrook-intervals-2026-09-11/verification/reviews/AV-01-review.md) and [submission record](../../references/colbrook-intervals-2026-09-11/README.md). The source archive identifies the drafts as AI-generated; authorship is recorded at the submitter's request. This is agent verification, not external human peer review or formal proof-assistant certification.

The difficulty, importance and rating rationale below are historical assessments of the original open target. The original statement and dated audits are preserved.
<!-- /colbrook-intervals -->

## Context and notation

Absolute values and vector inequalities are componentwise. All algorithmic questions use rational input in binary and the deterministic Turing model. Input length includes the matrix dimensions and the bit lengths of all rational coefficients.

## Problem statement

For input $A\in\mathbb Q^{n\times n}$ and $b\in\mathbb Q^n$, $n\ge1$, set

$$
\Sigma_+(A,b)=\{x\in\mathbb R^n:Ax+|x|=b\}.
$$

### Question

Classify the computational complexity of deciding whether

$$
|\Sigma_+(A,b)|=2^n.
$$

In particular, is this decision problem in $\mathsf P$, or can an $\mathsf{NP}$-hardness or $\mathsf{coNP}$-hardness classification be established by polynomial-time many-one reductions? The task returns one Boolean answer. Infinite solution sets are negative instances. There is no promise that the solution set is finite.

## Reference

Milan Hladík, [*Absolute value equations with $2^n$ solutions*](https://doi.org/10.1007/s11590-025-02251-z), Optimization Letters **20** (2026), 559–575, §2.3 and §7. The paper provides structural characterizations but explicitly leaves this recognition complexity open. Proposition 9 treats the subclass $\rho(|A|)<1$.

## Earlier status evidence — 2026-09-08

The version of record appeared October 6, 2025, in the April 2026 issue. Searches for the title with “complexity”, “solved”, and “2026”, and for “Hladík $2^n$ complexity”, found no subsequent classification. No separate arXiv version was located. The related result about more than $2^{n-1}$ solutions concerns a different threshold and does not settle this question.

## Audit update — 2026-09-10

Rechecked Hladík's [journal paper](https://link.springer.com/article/10.1007/s11590-025-02251-z), §2.3, which explicitly leaves maximum-count recognition open. Searches for later complexity results found no classification of the displayed problem. Its theorem on having more than $2^{n-1}$ solutions addresses a different threshold and does not solve exact $2^n$ recognition.
