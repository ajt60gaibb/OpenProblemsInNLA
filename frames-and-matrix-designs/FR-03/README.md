# FR-03 — Uniform conditioning of large Paley-frame column subsets

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Last checked:** 2026-09-08

**Status:** source-stated conjecture; no unconditional resolution found in screening on 2026-09-08.

For a prime $p\equiv1\pmod4$, let $Q$ be the nonzero quadratic residues modulo $p$, and set $N=(p+1)/2$. Define $\Phi_p\in\mathbb C^{N\times(p+1)}$ with row labels $\{0\}\cup Q$ and column labels $\{0,\ldots,p-1,\infty\}$ by
$$
(\Phi_p)_{0j}=p^{-1/2},\qquad
(\Phi_p)_{rj}=\sqrt{2/p}\exp(-2\pi\mathrm i rj/p)
\quad(r\in Q,\ 0\leq j<p),
$$
and $(\Phi_p)_{0,\infty}=1$, $(\Phi_p)_{r,\infty}=0$ for $r\in Q$. All columns have Euclidean norm one.

Do constants $0<\varepsilon<1/2$, $c>0$, $C<\infty$, and $p_0$ exist such that, for every prime $p\geq p_0$ with $p\equiv1\pmod4$ and every column subset $S$ with
$$
1\leq |S|\leq \lfloor c p^{1/2+\varepsilon}\rfloor,
$$
the column submatrix satisfies
$$
\kappa_2((\Phi_p)_S)
=\frac{\sigma_{\max}((\Phi_p)_S)}
{\sigma_{\min}((\Phi_p)_S)}\leq C?
$$
The condition number is infinite when the columns are dependent. Constants must be independent of both $p$ and $S$.

This is the bounded-condition-number formulation of the Paley-frame conjecture in Randomstrasse 101, Conjecture 29. It asks for uniform conditioning beyond the square-root sparsity scale, rather than conditioning of a random subset. The explicit frame would provide deterministic measurement matrices with stable sparse least-squares subproblems. The general deterministic restricted-isometry construction problem does not require this particular matrix, so neither problem duplicates the other.

## References

1. A. S. Bandeira, D. Dmitriev, K. Lucca, P. Nizić-Nikolac, and A. Rödder, *Randomstrasse 101: Open Problems of 2025*, arXiv:2603.29571 (2026), Conjecture 29 and the preceding Paley construction. [Paper](https://arxiv.org/html/2603.29571v1).
2. A. S. Bandeira, M. Fickus, D. G. Mixon, and P. Wong, *The road to deterministic matrices with the restricted isometry property*, Journal of Fourier Analysis and Applications 19 (2013), pp. 1123–1149. The Paley ETF discussion supplies the original restricted-isometry motivation. [Paper](https://arxiv.org/abs/1202.1234).
3. S. Satake, *On the restricted isometry property of the Paley matrix*, Linear Algebra and its Applications 631 (2021), pp. 35–47. Its main implication is conditional on a Paley-graph conjecture. [Paper](https://arxiv.org/abs/2011.02907).

## Status check — 2026-09-08

Searched “Paley matrix RIP conjecture 2025 2026”, “Paley ETF condition number square root bottleneck”, and the exact Satake title; checked the 2026 restatement and current arXiv records. No unconditional proof or counterexample was found. Conditional graph-discrepancy implications do not settle the quantifiers above.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
