# MD-06 — Global synchronization of a random cubic graph

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Provenance:** source-stated conjecture, with the phase domain written explicitly as a torus.  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** Controlling every local minimum on sparse random cubic graphs requires new landscape analysis beyond existing dense and high-degree results; it informs synchronization and nonconvex optimization.


For each even integer $n\geq4$, let $G_n$ be uniformly distributed over the labelled simple $3$-regular graphs with vertex set $\{1,\ldots,n\}$. For a graph $G$ on these vertices, define
$$
E_G(\theta)=
\sum_{\{i,j\}\in E(G)}
\bigl(1-\cos(\theta_i-\theta_j)\bigr),
\qquad
\theta\in(\mathbb R/2\pi\mathbb Z)^n.
$$
A phase vector is synchronized if $\theta_i=\theta_j$ modulo $2\pi$ for every pair $i,j$. A local minimum is understood with respect to the usual topology on the phase torus; it need not be strict.

Is it true that
$$
\lim_{\substack{n\to\infty\\ n\ {\rm even}}}
\mathbb P\!\left(
\text{every local minimum of }E_{G_n}
\text{ is synchronized}
\right)=1?
$$

The energy is a sparse graph optimization problem whose derivatives involve weighted graph Laplacians. The conjecture asks whether a typical graph of the smallest plausible fixed regular degree has no nonsynchronized local minima.

## References

1. A. S. Bandeira, A. Kireeva, A. Maillard, and A. Rödder, *Randomstrasse101: Open Problems of 2024*, arXiv:2504.20539 (2025), Definition 2.1 and Conjecture 3. [Paper](https://arxiv.org/html/2504.20539v1).
2. P. Abdalla, A. S. Bandeira, M. Kassabov, V. Souza, S. H. Strogatz, and A. Townsend, *Expander graphs are globally synchronizing*, Advances in Mathematics 488 (2026), article 110773; arXiv:2210.12788v4, introduction and Section 7. The random regular result requires substantially larger fixed degree. [Paper](https://arxiv.org/abs/2210.12788).
3. V. Jain, C. Mizgerd, and M. Sawhney, *The random graph process is globally synchronizing*, arXiv:2501.12205 (2025), Theorem 1.2: the connectivity hitting-time result for a different random graph model. [Paper](https://arxiv.org/abs/2501.12205).
4. S. Lepsveridze and S. Zhang, *Graphs with connectivity $3/4-\varepsilon$ are globally synchronizing*, (2026), dense minimum-degree result. [Paper](https://arxiv.org/abs/2608.20010).

## Status check — 2026-09-10

checked the current records 2504.20539v1 (2025-04-29), 2210.12788v4 (2026-01-19), 2501.12205v1 (2025-01-21), and 2608.20010v1 (2026-08-20), and searched “random cubic globally synchronizing 2026” and “random regular graphs degree 3 conjecture”. The large-degree, random-graph-process, and dense minimum-degree results do not establish the stated cubic-graph assertion. No proof, counterexample, or relevant withdrawal was found. The source's angular variables give the torus used here; its isolated sphere notation is not imposed on the phases.

**Audit update (2026-09-10):** Rechecked the 2025 cubic-graph conjecture and August 2026 dense-degree theorem, and searched for later cubic synchronization results. The dense threshold result concerns a different graph regime and does not resolve this target. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
