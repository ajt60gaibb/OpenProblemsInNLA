# TR-17 — Frobenius inner products minimize the algebraic complexity of rank-one approximation

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Last checked:** 2026-09-08

## Statement

Fix integers $k\ge1$, $n_j\ge2$, $d_j\ge1$, with $\sum_jd_j\ge3$. Set
$$
W_{\mathbb R}=\bigotimes_{j=1}^k\operatorname{Sym}^{d_j}(\mathbb R^{n_j}),\qquad
X=\{c\,v_1^{\otimes d_1}\otimes\cdots\otimes v_k^{\otimes d_k}:c\in\mathbb C,\ v_j\in\mathbb C^{n_j}\}\subset W_{\mathbb C}.
$$
For a positive definite symmetric real bilinear form $Q$ on $W_{\mathbb R}$, extend it complex-bilinearly. Define $\operatorname{ED}_Q(X)$ to be the number of complex critical points on the smooth nonzero part of $X$ of $Z\mapsto Q(A-Z,A-Z)$, for Zariski-generic $A\in W_{\mathbb C}$, with algebraic multiplicities.

Let $Q_F$ be the restriction of the entrywise Frobenius inner product from the full tensor product, with standard Euclidean inner products on the factors. Is
$$
\operatorname{ED}_Q(X)\ge\operatorname{ED}_{Q_F}(X)
$$
true for every such $Q$? The bilinear complexification uses no complex conjugates; the Frobenius restriction includes the usual repeated-entry weights on symmetric tensors.

## Relevance

The ED degree counts algebraic stationary solutions of weighted rank-one approximation. The conjecture says the natural tensor metric minimizes this complexity, across arbitrary positive definite weights and partial symmetries.

## References

1. K. Kozhasov, A. Muniz, Y. Qi, and L. Sodomaco, *On the minimal algebraic complexity of the rank-one approximation problem for general inner products*. [Primary text](https://arxiv.org/html/2309.15105v3), Conjecture 3.9; Theorem 3.12 and §4; [publication DOI](https://doi.org/10.1090/mcom/4176).
2. J. Draisma, E. Horobeţ, G. Ottaviani, B. Sturmfels, and R. R. Thomas, *The Euclidean distance degree of an algebraic variety*, Found. Comput. Math. (2016). [Primary preprint](https://arxiv.org/pdf/1309.0049), §§1–2 for ED degree and §4 for average ED degree.

## Status check — 2026-09-08

The October 13, 2025 revision of reference 1 explicitly retains Conjecture 3.9. It proves local minimality for all these varieties and global minimality for matrices, binary symmetric tensors, and ternary symmetric cubics. Searches `"Frobenius" "ED degree" "conjecture" "2026"` and the exact paper title with `proof` located no general resolution. This bounded check distinguishes global minimality from the proved local theorem.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
