# TR-17 — Frobenius inner products minimize the algebraic complexity of rank-one approximation

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because local minimality of ED degree must be strengthened to a global comparison across all positive definite metrics; community importance concerns weighted approximation and partially symmetric tensor models.  
**Last checked:** 2026-09-11  
**Status:** Solved  

<!-- colbrook-tensor-metrics-rank -->
**Affirmative resolution recorded 2026-09-11.** Matthew J. Colbrook's [complete manuscript, Theorem 1](../../references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr17_solution.pdf) ([LaTeX source](../../references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr17_solution.tex)) proves the stated global inequality for every permitted Segre–Veronese format and every positive definite real symmetric bilinear form, with the complex-bilinear critical-point and multiplicity convention below. The proof gives nonnegative weights for a Chern–Schwartz–MacPherson coefficient comparison and proves the needed signed Euler-characteristic positivity even for singular or nonreduced quadric sections. No genericity restriction on the metric is imposed. The full original source passed an [independent mathematical agent review](../../references/colbrook-tensor-metrics-rank-2026-09-11/verification/reviews/TR-17-review.md). [Submission and verification record](../../references/colbrook-tensor-metrics-rank-2026-09-11/README.md). This is documented AI-assisted verification, not external human peer review; no priority claim is made. The original target and former difficulty and importance ratings are retained below as historical context.
<!-- /colbrook-tensor-metrics-rank -->

## Statement

Fix integers $`k\ge1`$, $`n_j\ge2`$, $`d_j\ge1`$, with $`\sum_jd_j\ge3`$. Set

```math
W_{\mathbb R}=\bigotimes_{j=1}^k\mathop{\mathrm{Sym}}\nolimits^{d_j}(\mathbb R^{n_j}),\qquad
X=\{c\,v_1^{\otimes d_1}\otimes\cdots\otimes v_k^{\otimes d_k}:c\in\mathbb C,\ v_j\in\mathbb C^{n_j}\}\subset W_{\mathbb C}.
```

For a positive definite symmetric real bilinear form $`Q`$ on $`W_{\mathbb R}`$, extend it complex-bilinearly. Define $`\mathop{\mathrm{ED}}\nolimits_Q(X)`$ to be the number of complex critical points on the smooth nonzero part of $`X`$ of $`Z\mapsto Q(A-Z,A-Z)`$, for Zariski-generic $`A\in W_{\mathbb C}`$, with algebraic multiplicities.

Let $`Q_F`$ be the restriction of the entrywise Frobenius inner product from the full tensor product, with standard Euclidean inner products on the factors. Is

```math
\mathop{\mathrm{ED}}\nolimits_Q(X)\ge\mathop{\mathrm{ED}}\nolimits_{Q_F}(X)
```

true for every such $`Q`$? The bilinear complexification uses no complex conjugates; the Frobenius restriction includes the usual repeated-entry weights on symmetric tensors.

## Relevance

The ED degree counts algebraic stationary solutions of weighted rank-one approximation. The conjecture says the natural tensor metric minimizes this complexity, across arbitrary positive definite weights and partial symmetries.

## References

1. K. Kozhasov, A. Muniz, Y. Qi, and L. Sodomaco, *On the minimal algebraic complexity of the rank-one approximation problem for general inner products*. [Primary text](https://arxiv.org/html/2309.15105v3), Conjecture 3.9; Theorem 3.12 and §4; [publication DOI](https://doi.org/10.1090/mcom/4176).
2. J. Draisma, E. Horobeţ, G. Ottaviani, B. Sturmfels, and R. R. Thomas, *The Euclidean distance degree of an algebraic variety*, Found. Comput. Math. (2016). [Primary preprint](https://arxiv.org/pdf/1309.0049), §§1–2 for ED degree and §4 for average ED degree.

## Status check — 2026-09-10

Rechecked [Kozhasov et al. v3, Conjecture 3.9, Theorem 3.12 and §5](https://arxiv.org/html/2309.15105v3), and searched for a later general proof. Global minimality is proved for binary symmetric tensors and ternary symmetric cubics, which occur in this target; the matrix theorem concerns excluded order two. Local minimality is known generally but does not prove the requested global inequality. No full resolution was located.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
