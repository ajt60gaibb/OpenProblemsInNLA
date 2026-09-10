# SP-10 — The graph complement conjecture for minimum symmetric rank

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Extreme reflects a longstanding bound over all symmetric sparsity patterns, still beyond the available general rank estimates. Community impact comes from its central role in graph inverse eigenvalue problems and complementary low-rank realizations.

## Problem statement

For a finite simple undirected graph $G$ with vertex set $\{1,\ldots,n\}$, $n\ge1$, define
$$
\mathcal S(G)=\{A\in\mathbb R^{n\times n}:A=A^T,\ \mathcal G(A)=G\},
\qquad
\operatorname{mr}(G)=\min_{A\in\mathcal S(G)}\operatorname{rank}A.
$$
Here $\mathcal G(A)$ has an edge $\{i,j\}$ exactly when $i\ne j$ and $a_{ij}\ne0$. Diagonal entries are unrestricted. Let $G^c$ have exactly the complementary edges between distinct vertices. Does every such graph satisfy
$$
\operatorname{mr}(G)+\operatorname{mr}(G^c)\le n+2?
$$

## Relevance and ratings

 This is a structured low-rank feasibility problem for complementary symmetric sparsity patterns. Because diagonal shifts preserve those patterns, minimum rank also determines the largest eigenvalue multiplicity realizable with a prescribed off-diagonal pattern. It is an inverse eigenvalue problem, not a claim about the rank of the unweighted adjacency matrix.

## References

- F. Barioli, S. M. Fallat, H. Gupta, and Z. Li, *The weak version of the graph complement conjecture and partial results for the delta conjecture*, Discrete Mathematics 349 (2026), 114861, Conjecture 1.1 ([primary manuscript](https://arxiv.org/html/2505.24577v1); [journal](https://doi.org/10.1016/j.disc.2025.114861)).
- S. M. Fallat and L. Hogben, *The minimum rank of symmetric matrices described by a graph: A survey*, Linear Algebra and its Applications 426 (2007), 558–582, introduction and discussion of minimum rank ([primary manuscript](https://aimath.org/WWN/matrixspectrum/FallatHogbenMinRank07.pdf); [journal](https://doi.org/10.1016/j.laa.2007.05.036)).

- M. Jansrang and S. K. Narayan, *Graph complement conjecture for classes of shadow graphs*, Operators and Matrices 15 (2021), 589–614, §1 and Theorem 1 ([primary paper](https://files.ele-math.com/articles/oam-15-40.pdf); [journal](https://doi.org/10.7153/oam-2021-15-40)).

## Status check

 The 2026 paper resolves a weak version with a coefficient strictly below $2$ in front of $n$, not the displayed coefficient $1$. Searches for “graph complement conjecture”, “minimum rank”, “solved”, “proof”, and 2025–2026 found no general resolution. The source's May 2025 arXiv version and the 2026 journal record were checked. No positive-semidefinite or strong-Arnold variant is separately counted here.

## Audit update — 2026-09-10

**Partially resolved:** trees, unicyclic graphs, chordal graphs and partial 3-trees satisfy the stronger real positive-semidefinite version; Jansrang–Narayan §1 records these results and Theorem 1 proves additional shadow-graph families. Since unrestricted minimum rank is no larger than PSD minimum rank, these are cases of the displayed target. The general graph case remains the unresolved question. The full primary manuscript and 2026 publication record above, the 2021 paper, and targeted later-resolution searches were checked; no full resolution was located.
