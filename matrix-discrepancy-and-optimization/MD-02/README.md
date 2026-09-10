# MD-02 — The sharp Lovász-theta constant for random circulant graphs

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** The Fourier-constrained random optimization problem needs sharper analysis than current order bounds; it matters to structured matrix optimization and sampling.


For each $n\ge2$, partition $\mathbb Z_n\setminus\{0\}$ into classes $\{s,-s\}$ (a singleton when $s=-s$). Select each class independently with probability $1/2$ and let $S$ be their union. Form the simple undirected graph $G_n$ on $\mathbb Z_n$ with $\{i,j\}$ an edge exactly when $i-j\in S$.

For any graph on $n$ vertices put
$$
\vartheta(G)=\max\Bigl\{\sum_{i,j}X_{ij}:X\in\mathbb R^{n\times n},\ X=X^T\succeq0,\ \operatorname{tr}X=1,\ X_{ij}=0\text{ if }\{i,j\}\in E(G)\Bigr\}.
$$
**Conjecture.** $\displaystyle\lim_{n\to\infty}\mathbb E\vartheta(G_n)/\sqrt n=1$.

Cyclic symmetry reduces this semidefinite program to a linear program involving the discrete Fourier matrix, connecting its typical optimum with structured sampling.

## References

1. A. S. Bandeira, D. Dmitriev, K. Lucca, P. Nizić-Nikolac, and A. Rödder, *Randomstrasse101: Open Problems of 2025*, Entry 9, Conjecture 18. [Archived paper](https://arxiv.org/abs/2603.29571).
2. A. S. Bandeira, J. Błasiok, D. Dmitriev, U. Faure, A. Kireeva, and D. Kunisky, *The Lovász number of random circulant graphs*, SampTA 2025. [Paper](https://arxiv.org/abs/2502.16227); [published DOI](https://doi.org/10.1109/SampTA64769.2025.11133544).

## Status check — 2026-09-10

The 2026 collection retains the conjecture and cites the 2025 partial bounds, including an upper bound of order $\sqrt{n\log\log n}$. Searches for subsequent sharp asymptotics and resolutions found none. Independent edge sampling on all vertex pairs is the different ensemble in MD-01.

**Audit update (2026-09-10):** Rechecked the 2026 Conjecture 18 and the SampTA paper, then searched for sharp random-circulant asymptotics. Added the published DOI; the remaining logarithmic upper-bound factor does not settle the limit. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
