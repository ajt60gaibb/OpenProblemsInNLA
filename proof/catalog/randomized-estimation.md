# Randomly pivoted factorizations

> Legacy source map and screening notes. Admitted statements have moved to category/problem folders. Follow the links below or [browse the new index](../../CATALOG.md). Shared notation and uncounted material are retained here as the historical source record.

This chapter contains **3 admitted problems**. Literature checks were
performed on **2026-09-08** and establish provisional open status, not an
exhaustive proof that no solution exists. Ratings are editorial assessments.

## Randomly pivoted Cholesky notation

For a Hermitian positive-semidefinite $A\in\mathbb C^{n\times n}$, define
the exact-arithmetic RPCholesky residuals by $R_0=A$. Conditional on
$R_t\ne0$, select $j$ with probability $(R_t)_{jj}/\operatorname{tr}(R_t)$
and set

$$
R_{t+1}=R_t-\frac{R_t(:,j)R_t(j,:)}{(R_t)_{jj}}.
$$

If $R_t=0$, keep all subsequent residuals zero. Eigenvalues are ordered
$\lambda_1(A)\geq\cdots\geq\lambda_n(A)\geq0$, and
$\tau_r(A)=\sum_{j>r}\lambda_j(A)$. This is the pivot rule in Chen,
Epperly, Tropp, and Webber, [*Randomly pivoted Cholesky: Practical
approximation of a kernel matrix with few entry evaluations*](https://doi.org/10.1002/cpa.22234),
Algorithm 1; their Lemma 5.5 gives the current comparison
$\mathbb E\operatorname{tr}(R_r)\leq2^r\tau_r(A)$.

<a id="ra-01"></a>

## RA-01 — Optimal pivot count for RPCholesky trace approximation

[Open the problem folder](../../randomized-and-low-rank-approximation/RA-01/README.md) · [PDF](../../randomized-and-low-rank-approximation/RA-01/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/RA-01/problem.tex)


<a id="ra-02"></a>

## RA-02 — Polynomial trace-error factor after exactly the target rank of pivots

[Open the problem folder](../../randomized-and-low-rank-approximation/RA-02/README.md) · [PDF](../../randomized-and-low-rank-approximation/RA-02/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/RA-02/problem.tex)


<a id="ra-03"></a>

## RA-03 — Improve the randomized LU squared-error factor to $2^k$

[Open the problem folder](../../randomized-and-low-rank-approximation/RA-03/README.md) · [PDF](../../randomized-and-low-rank-approximation/RA-03/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/RA-03/problem.tex)


## Excluded and uncounted leads

- Dissertation Conjecture 11.3 is covered by the spectral-error theorem in
  [Epperly's August 2026 paper](https://arxiv.org/html/2608.20633v1),
  Theorem 1.4. Its discussion also gives a logarithmic obstruction to
  removing the effective-dimension logarithm.
- The dissertation's §20.1–20.3 directions, pp. 299–303, request sharper
  estimation bounds, indefinite-Hermitian methods, and stable subspace
  downdating. They lack explicit error or stability targets sufficient for
  admission here. Relevant later progress includes Hallman's
  [*Two Variations on the XTrace Algorithm*](https://arxiv.org/html/2512.02316v1),
  especially §§4 and 6, and Lazzarino, Pearce, and Pritchard's
  [*Efficient error estimators for Generalized Nyström*](https://arxiv.org/html/2601.11493v1).
- The dissertation's p. 185 dimension-independent column-Nyström
  Frobenius-error existence question is not admitted. Published lower
  bounds already obstruct that guarantee: Wang, Zhang, and Zhang,
  [*Towards More Efficient SPSD Matrix Approximation and CUR Matrix
  Decomposition*](https://www.jmlr.org/papers/volume17/15-190/15-190.pdf),
  Theorem 7 and the paragraph following it, p. 14, recover the
  $\Omega(1+rn/c^2)$ squared-error ratio for $c$ selected columns and cite
  Wang and Zhang (2013) as the original Nyström lower bound.
