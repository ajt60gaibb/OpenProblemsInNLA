# RA-05 — Sharp joint rank and accuracy dependence for strong $\ell_p$ subspace coresets

**Difficulty:** hard  
**Importance:** interesting to the community  
**Last checked:** 2026-09-08

**Status:** source-stated open question; no resolution found in screening on 2026-09-08.

Fix a real $p>2$. For $A\in\mathbb R^{n\times d}$, with rows $a_i^T$, and a linear subspace $F\subseteq\mathbb R^d$, define
$$
\operatorname{cost}_A(F)=\sum_{i=1}^n\|a_i^T(I-P_F)\|_2^p,
$$
where $P_F$ is the Euclidean orthogonal projector. A strong row coreset consists of nonnegative weights $w_1,\ldots,w_n$, supported on a small subset of the original rows, for which
$$
(1-\varepsilon)\operatorname{cost}_A(F)
\leq\sum_iw_i\|a_i^T(I-P_F)\|_2^p
\leq(1+\varepsilon)\operatorname{cost}_A(F)
$$
holds simultaneously for every $F$ of dimension at most $k$.

Determine the optimal worst-case coreset size as a joint function of $k$ and $\varepsilon$, up to logarithmic factors. In particular, do constants $C_p,c_p>0$ exist such that, for all $n,d$, integers $1\leq k<d$, all input matrices $A$, and all $0<\varepsilon<1/2$, such a coreset exists with
$$
|\operatorname{supp}(w)|\leq
C_p\left(\frac{k^{p/2}}{\varepsilon}+\frac{k}{\varepsilon^2}\right)
\log^{c_p}\!\left(\frac{2k}{\varepsilon}\right)?
$$
The constants may depend on fixed $p$, but not on $n,d,k,\varepsilon$. This is an existence/size question; no extra running-time target is imposed.

Such a coreset permits subsequent robust low-rank fitting on a much smaller weighted matrix. The August 2026 paper proves an upper bound of order $\widetilde O_p(k^{p/2}/\varepsilon^2)$ and explicitly identifies the remaining gap to the joint lower-bound expression in Section 1.4. Its new result supersedes older questions that merely asked for an $\varepsilon^{-2}$ dependence.

## References

1. H. Lin, V. Mirrokni, and D. P. Woodruff, *Nearly Optimal Strong Coresets for $\ell_p$ Subspace Approximation*, arXiv:2608.26047v2, Section 1.4 “Open problems”; Section 1.2 for the new bounds. [Paper](https://arxiv.org/html/2608.26047v2).
2. D. P. Woodruff and T. Yasuda, *Root ridge leverage score sampling for $\ell_p$ subspace approximation*, FOCS 2025, full version arXiv:2407.03262. [Paper](https://arxiv.org/abs/2407.03262).

## Status check — 2026-09-08

Searched “strong coresets subspace approximation p greater than 2 epsilon 2026” and the exact 2026 title; checked the latest arXiv v2 of August 27, 2026. No later resolution was found. The target comes from the remaining question in that paper, rather than its already improved predecessor bounds.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
