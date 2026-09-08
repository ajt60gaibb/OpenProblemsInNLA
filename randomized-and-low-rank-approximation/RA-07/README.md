# RA-07 — Convexity of the expected error of volume-sampled column subsets

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Last checked:** 2026-09-08

**Status:** source-stated conjecture; no resolution found in screening on 2026-09-08.

For $n\geq3$ and positive real numbers $\lambda_1,\ldots,\lambda_n$, let
$$
e_j(\lambda)=\sum_{\substack{S\subseteq\{1,\ldots,n\}\\|S|=j}}
\prod_{i\in S}\lambda_i,
\qquad e_0=1,\quad e_{n+1}=0.
$$
Define $f(j)=(j+1)e_{j+1}(\lambda)/e_j(\lambda)$ for $1\leq j\leq n$. Is $f$ discretely convex, that is,
$$
f(j-1)-2f(j)+f(j+1)\geq0
\qquad(2\leq j\leq n-1),
$$
for every such $n$ and positive tuple $\lambda$?

For a matrix $A$ with positive eigenvalues $\lambda_i$ of $A^TA$, sample a set $S$ of $j$ columns with probability proportional to $\det(A_S^TA_S)$. Its expected squared Frobenius projection error is
$$
\mathbb E\|(I-P_{A_S})A\|_F^2=f(j),
$$
where $P_{A_S}$ is the orthogonal projector onto the selected column span. Thus the conjecture asserts a diminishing marginal improvement in the average reconstruction error of these fixed-size determinantal samples. It is distinct from optimizing a worst-case approximation factor over all matrices with a prescribed spectrum.

## References

1. M. Dereziński, R. Khanna, and M. W. Mahoney, *Improved guarantees and a multiple-descent curve for Column Subset Selection and the Nyström method*, NeurIPS 2020, arXiv:2002.09073. Section 5, Conjecture 1 is exactly the discrete-convexity statement. [Paper](https://arxiv.org/abs/2002.09073).
2. A. Deshpande, L. Rademacher, S. S. Vempala, and G. Wang, *Matrix Approximation and Projective Clustering via Volume Sampling*, Theory of Computing 2 (2006), Article 12, pp. 225–247. See the volume-sampling matrix approximation results. [Paper](https://theoryofcomputing.org/articles/v002a012/).

## Status check — 2026-09-08

Searched “Derezinski Khanna Mahoney Conjecture 1 convexity”, “elementary symmetric ratio $k+1$ convexity DPP”, and the exact 2020 paper title with 2025/2026. Checked the current arXiv record. No proof or counterexample was found. Standard Newton inequalities imply other ratio inequalities but are not cited as a resolution of this second-difference inequality.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
