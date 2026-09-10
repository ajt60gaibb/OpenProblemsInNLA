# PF-02 — Connectedness of minimal positive semidefinite factorization orbits

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because topology of optimal PSD factorizations must be controlled beyond size two; community importance concerns nonuniqueness and separated solution families in constrained factorization algorithms.  
**Status:** Open  
**Area:** geometry of constrained matrix factorizations  
**Last checked:** 2026-09-10  

## Context and notation

Write $\mathbb S_+^k$ for the cone of real symmetric positive semidefinite $k\times k$ matrices. For an entrywise nonnegative matrix $M\in\mathbb R_+^{p\times q}$, its **real positive semidefinite rank** is

$$
\operatorname{rank}_{\rm psd}(M)
=\min\{k\ge1:\ \exists A_1,\ldots,A_p,B_1,\ldots,B_q\in\mathbb S_+^k,\quad
M_{ij}=\operatorname{tr}(A_iB_j)\ \text{for all }i,j\}.
$$

This definition concerns a family of matrix factors indexed by the rows and columns of $M$.

## Problem statement

Let $k\ge3$ and $p,q\ge1$ be integers. Suppose $M\in\mathbb R_+^{p\times q}$ satisfies

$$
\operatorname{rank}(M)=\frac{k(k+1)}2,
\qquad \operatorname{rank}_{\rm psd}(M)=k.
$$

Let $\mathcal F_k(M)$ be the set of all tuples $(A_1,\ldots,A_p,B_1,\ldots,B_q)$ in $(\mathbb S_+^k)^{p+q}$ satisfying $\operatorname{tr}(A_iB_j)=M_{ij}$ for every $i,j$. Give it the Euclidean subspace topology. Identify tuples under the changes of basis

$$
A_i\longmapsto S^\mathsf T A_iS,\qquad
B_j\longmapsto S^{-1}B_jS^{-\mathsf T},
\qquad S\in GL(k,\mathbb R).
$$

Give the resulting orbit space the quotient topology.

### Question

Is $\mathcal F_k(M)/GL(k,\mathbb R)$ connected for every $M$ satisfying these hypotheses?

The ordinary-rank hypothesis is part of the problem. The case $k=2$ is known to be connected. The question asks whether optimal factors can belong to separated families after changes of basis are identified.

## References

Fawzi, Gouveia, Parrilo, Robinson, and Thomas, [*Positive semidefinite rank*](https://arxiv.org/html/1407.4095), §9.2, Problem 9.4. Richard Z. Robinson, [*The Positive Semidefinite Rank of Matrices and Polytopes*](https://digital.lib.washington.edu/server/api/core/bitstreams/4e9d6133-5d14-4071-9905-70bd7dfd530e/content), University of Washington dissertation (2015), Chapter 7, especially Proposition 7.0.8.

## Status check — 2026-09-10

Rechecked [Fawzi et al., §9.2, Problem 9.4](https://arxiv.org/html/1407.4095), including the ordinary-rank hypothesis, and searched for connectedness of PSD factorization orbits. No resolution for k at least three was located. The proved k=2 case is excluded here; disconnected nonnegative factorizations do not automatically remain disconnected in the PSD orbit space. No recent primary reaffirmation of the exact higher-size question was found.

