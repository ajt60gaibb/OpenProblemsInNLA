# RA-11 — Optimal trace-estimation complexity using Kronecker matrix-vector queries

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because optimal adaptive information bounds remain unknown even across exponential tensor-order scales; community impact is reliable computation with tensor-structured matrix access.  
**Topic:** Structured randomized trace estimation.  
**Last checked:** 2026-09-10  
**Status:** Open  

Let $`n,q\ge2`$ be integers and $`0<\varepsilon<1/2`$. An unknown real symmetric PSD matrix $`M\in\mathbb R^{n^q\times n^q}`$ is accessible only through an exact oracle which, on input $`v_1,\ldots,v_q\in\mathbb R^n`$, returns

```math
M(v_1\otimes\cdots\otimes v_q)\in\mathbb R^{n^q}.
```

Let $`Q(n,q,\varepsilon)`$ be the smallest integer $`t`$ for which a randomized algorithm can, for every such $`M`$, make at most $`t`$ oracle calls and output $`\widehat t\in\mathbb R`$ satisfying

```math
\Pr\bigl\{|\widehat t-\mathop{\mathrm{tr}}\nolimits(M)|\le\varepsilon\mathop{\mathrm{tr}}\nolimits(M)\bigr\}\ge\frac23.
```

Queries may depend on previous responses and internal randomness. The algorithm may perform arbitrary finite exact arithmetic between calls; only oracle calls are counted. The inputs $`n,q,\varepsilon`$ are known. Neither the query vectors nor their concatenation are required to have bounded condition number, and there is no restriction to Hutchinson estimators.

Determine $`Q(n,q,\varepsilon)`$ up to universal constant factors, simultaneously in all three parameters.

This is a precise query-complexity formulation of the source's request for tight trace-estimation bounds. It would quantify the cost of exploiting rank-one tensor queries when ordinary matrix access is unavailable.

## References

1. R. A. Meyer, W. Swartworth, and D. P. Woodruff, [Understanding the Kronecker Matrix-Vector Complexity of Linear Algebra](https://arxiv.org/html/2502.08029v2), ICML 2025, PMLR 267, 43909–43933. Definition 1 specifies the oracle; §6, final sentence, asks for tight trace-estimation bounds. Theorem 7 bounds a conditioned scalar quadratic-form oracle; its following discussion distinguishes full-vector responses. [Published record](https://proceedings.mlr.press/v267/meyer25a.html).
2. R. A. Meyer and H. Avron, [Hutchinson's Estimator is Bad at Kronecker-Trace-Estimation](https://arxiv.org/abs/2309.04952), *SIAM Journal on Matrix Analysis and Applications* 47 (2026), 353–387, abstract and trace-estimator bounds. These tight rates concern the specified estimator and query distributions.

## Status check — 2026-09-08

Checked the first paper's latest listed arXiv v2 (2025-02-13), §6, and its ICML publication record; checked the second paper's latest listed v2 (2025-01-31) and 2026 journal record. Searches for “Kronecker trace estimation tight 2026” and the exact first title found no solution for unrestricted adaptive algorithms. The available trace lower bound assumes both scalar quadratic-form queries and bounded query conditioning; it does not establish a lower bound for the unrestricted full-vector oracle defined here. The 2026 Hutchinson article establishes estimator-specific rates and therefore does not determine $`Q`$. The minimax definition and explicit parameter range are editorial formalization of a source-stated complexity question, not a quoted formula from the paper.

## Audit — 2026-09-10

Rechecked [Meyer–Swartworth–Woodruff, §6](https://arxiv.org/html/2502.08029v2) and the [2026 Hutchinson publication](https://doi.org/10.1137/24M1720895). Kronecker-trace-complexity searches found no unrestricted adaptive characterization. Conditioned scalar-query lower bounds and estimator-specific rates still do not settle the full-vector oracle.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
