# RA-20 — Critical-point counts for symmetric rank-two approximation with diagonal zeros

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Symmetric structured low-rank approximation  
**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Open  
**Last checked:** 2026-09-11

**Rating rationale:** Four linked formulas predict how diagonal constraints alter the algebraic complexity of rank-two approximation. A proof must handle the geometry of the constrained symmetric varieties uniformly in matrix order.

## Statement

For $s\in\{1,2,3,4\}$ and $n\ge\max\{3,s\}$, define

$$W_{n,s}=\{X\in\mathbb C^{n\times n}:X^{\mathsf T}=X,
\ \operatorname{rank}X\le2,\ x_{11}=\cdots=x_{ss}=0\}.$$

For generic symmetric $U\in\mathbb C^{n\times n}$, let $e_{n,s}$ be the number of complex critical points on the smooth locus of $W_{n,s}$ of

$$d_U(X)=\sum_i(x_{ii}-u_{ii})^2+
2\sum_{i<j}(x_{ij}-u_{ij})^2.$$

Generic means outside a proper algebraic exceptional set. A point is critical if the differential vanishes on its tangent space. Thus $e_{n,s}$ is the Euclidean distance degree for the bilinear extension of the **full Frobenius metric**; the off-diagonal terms have weight two, and complex conjugation is absent.

**Conjecture (Kubjas–Sodomaco–Tsigaridas, Conjecture 5.6, $n\ge3$).**

$$e_{n,s}=\begin{cases}
3(n-1)-2,&s=1,\\
9(n-2)-2,&s=2,\\
27(n-3)+4,&s=3,\\
81(n-4)+28,&s=4.
\end{cases}$$

All four zero counts form one target. The explicit $n\ge3$ restriction avoids a degenerate endpoint in the printed statement: when $n=2$, the rank bound is vacuous and both possible varieties are linear with ED degree one, whereas the displayed $s=2$ formula does not apply.

## Evidence and numerical significance

The source's Table 7 gives matching computations through order ten. These do not constitute an all-dimension proof. The problem counts stationary candidates for symmetric Frobenius approximation with prescribed diagonal zeros. It concerns fixed rank two, unlike [corank-one approximation in general square matrices](../RA-19/README.md).

## References and status check

- K. Kubjas, L. Sodomaco and E. Tsigaridas, *Exact solutions in low-rank approximation with zeros*, Linear Algebra and its Applications 641 (2022), 67–97. [DOI](https://doi.org/10.1016/j.laa.2022.01.021); [current author manuscript](https://arxiv.org/abs/2010.15636v2), 29 January 2022. Conjecture 5.6 and Table 7, manuscript p.21; §2 and §5 supply the distance convention.

On 2026-09-11, checked arXiv v2, publication lists and targeted searches for the paper title, symmetric zero patterns, Conjecture 5.6, Euclidean distance degree, and later proofs or counterexamples. No full resolution in the displayed range was found. Source formulas were compared with Table 7; the restriction excluding $n=2$ is stated above. The separate nonsymmetric formulas in Conjecture 5.2 have a table/label discrepancy and are not imported here. This is a bounded status check.
