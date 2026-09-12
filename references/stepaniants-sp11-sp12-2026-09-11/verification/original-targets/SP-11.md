# SP-11 — The delta conjecture for minimum symmetric rank

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Extreme reflects the longstanding all-graph gap between a local degree constraint and an exact matrix-realization guarantee. Community impact comes from controlling achievable eigenvalue multiplicity across symmetric sparsity patterns.

## Problem statement

Let $G$ be any finite simple undirected graph on $n\ge1$ vertices, and let $\delta(G)$ be its minimum vertex degree. Let $\mathcal S(G)$ consist of the real symmetric $n\times n$ matrices whose off-diagonal nonzero entries occur exactly at edges of $G$, with unrestricted diagonal entries.

Must there exist $A\in\mathcal S(G)$ such that
$$
\dim\ker A\ge\delta(G)?
$$
Equivalently, with $\operatorname{mr}(G)=\min_{A\in\mathcal S(G)}\operatorname{rank}A$, is
$$
\operatorname{mr}(G)\le n-\delta(G)
$$
valid for every $G$?

## Relevance and ratings

 This asks whether local sparsity information guarantees feasibility of a symmetric matrix with a specified large nullspace. It belongs to structured inverse eigenvalue and low-rank matrix construction. It does not prescribe the numerical edge weights, and does not require positive semidefiniteness.

## References

- F. Barioli, S. M. Fallat, H. Gupta, and Z. Li, *The weak version of the graph complement conjecture and partial results for the delta conjecture*, Discrete Mathematics 349 (2026), 114861, §1, paragraph immediately before Conjecture 1.5 ([primary manuscript](https://arxiv.org/html/2505.24577v1); [journal](https://doi.org/10.1016/j.disc.2025.114861)).
- S. M. Fallat and L. Hogben, *The minimum rank of symmetric matrices described by a graph: A survey*, Linear Algebra and its Applications 426 (2007), 558–582, minimum-rank definitions and inverse eigenvalue interpretation ([primary manuscript](https://aimath.org/WWN/matrixspectrum/FallatHogbenMinRank07.pdf); [journal](https://doi.org/10.1016/j.laa.2007.05.036)).

## Status check

 The 2026 article treats the original conjecture as open and establishes results under additional graph restrictions. Its numbered Conjecture 1.5 is a stronger positive-semidefinite/SAP statement; the present entry retains the original real symmetric formulation stated directly before it. Searches for “minimum rank”, “delta conjecture”, “proof”, and 2025–2026 found no general resolution. The stronger variants are not counted as additional problems.

## Audit update — 2026-09-10

**Partially resolved:** Barioli–Fallat–Gupta–Li, Theorem 2.11(a), proves the stronger bound $\nu(G)\ge\delta(G)$ for graphs of girth at least $11$ and minimum degree at least $4$. Parts (b)–(e) give further explicit girth and forbidden-subgraph regimes. These PSD/SAP witnesses also belong to the unrestricted symmetric class displayed here. The full primary manuscript, 2026 publication record and later-resolution searches were checked; no proof for all graphs was located.
