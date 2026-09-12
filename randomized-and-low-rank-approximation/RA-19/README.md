# RA-19 — Critical-point count for corank-one approximation with a fixed zero

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Structured low-rank approximation and Euclidean distance degree  
**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Open  
**Last checked:** 2026-09-11

**Rating rationale:** The target is an exact formula for a constrained approximation problem in every dimension. It would quantify the algebraic complexity of enumerating candidate nearest singular matrices with a prescribed zero.

## Statement

For $n\ge3$, let

$$V_n=\{X\in\mathbb C^{n\times n}:\det X=0,\ x_{11}=0\}.$$

For generic $U\in\mathbb C^{n\times n}$, consider the bilinear squared distance

$$d_U(X)=\sum_{i,j=1}^n(x_{ij}-u_{ij})^2.$$

Its critical points on the smooth locus of $V_n$ satisfy $\mathrm d(d_U)_X[Z]=0$ for every tangent vector $Z\in T_XV_n$. Their finite number for generic $U$, meaning outside a proper algebraic exceptional set, is the *Euclidean distance degree* $\operatorname{EDdeg}(V_n)$. There is no complex conjugation in this definition; over the reals the objective is squared Frobenius distance.

**Conjecture (Kubjas–Sodomaco–Tsigaridas, Conjecture 5.1, nontrivial dimensions).**

$$\operatorname{EDdeg}(V_n)=5n-7\qquad\text{for every }n\ge3.$$

The dimension restriction is explicit here: at $n=2$, the equations reduce to $x_{11}=0$ and $x_{12}x_{21}=0$, a union of two linear spaces with ED degree two. The printed conjecture omits a lower bound on $n$, while its supporting table begins at three. That exceptional endpoint is not asserted to satisfy the formula.

## Evidence and numerical significance

Table 2 of the source reports $8,13,18,23,28,33,38,43$ for $n=3,\ldots,10$, using numerical critical-point computations checked against symbolic ideal degrees. These finite computations support the conjecture but do not establish the formula for arbitrary $n$.

Truncated SVD solves unconstrained Frobenius approximation, but a fixed zero changes its critical equations. This target concerns corank-one approximation in general square matrices; the [symmetric rank-two zero-pattern problem](../RA-20/README.md) has different geometry and rank constraints.

## References and status check

- K. Kubjas, L. Sodomaco and E. Tsigaridas, *Exact solutions in low-rank approximation with zeros*, Linear Algebra and its Applications 641 (2022), 67–97. [DOI](https://doi.org/10.1016/j.laa.2022.01.021); [current author manuscript](https://arxiv.org/abs/2010.15636v2), 29 January 2022. Conjecture 5.1 and Table 2, manuscript p.19; §2 defines the critical-point and ED-degree conventions.

On 2026-09-11, checked the current arXiv version, the authors' publication lists, and targeted title, conjecture-number, ED-degree, proof and 2026 searches. No later proof or counterexample for $n\ge3$ was located. The formulation and table were checked in arXiv v2; a separate publisher PDF was not obtained. The scope correction at $n=2$ is disclosed above. This is a bounded literature check.
