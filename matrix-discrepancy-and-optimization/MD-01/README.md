# MD-01 — The sharp Lovász-theta constant for dense random graphs

**Difficulty:** challenging  
**Importance:** broadly interesting  
**Last checked:** 2026-09-08

**Status:** source-backed open problem; no resolution found in the bounded literature check.

Let $G_n$ be the simple random graph on $n$ labelled vertices in which each unordered pair is an edge independently with probability $1/2$. For a graph $G$, define its Lovász number by
$$
\vartheta(G)=\max\{\langle J,X\rangle:X\in\mathbb R^{n\times n},\ X=X^T\succeq0,\ \operatorname{tr}X=1,\ X_{ij}=0\text{ for }\{i,j\}\in E(G)\},
$$
where $J$ is the all-ones matrix and $\langle J,X\rangle=\sum_{i,j}X_{ij}$.

**Conjecture.** $\displaystyle\lim_{n\to\infty}\mathbb E\vartheta(G_n)/\sqrt n=1$.

This asks for the leading constant of a random semidefinite matrix optimization problem. It is an expectation statement; convergence in probability is not substituted for it.

## References

1. A. S. Bandeira, D. Dmitriev, K. Lucca, P. Nizić-Nikolac, and A. Rödder, *Randomstrasse101: Open Problems of 2025*, Entry 9, Conjecture 17 and the preceding SDP definition. [Archived paper](https://arxiv.org/abs/2603.29571).

## Status check — 2026-09-08

The archived 2026 paper retains the conjecture. Targeted searches for the Lovász number of dense Erdős–Rényi graphs and a sharp leading constant through September 2026 found no resolution. The adjacent circulant problem uses a different random matrix ensemble and is recorded separately.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
