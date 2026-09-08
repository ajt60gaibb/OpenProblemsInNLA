# Randomly pivoted factorizations

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

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** randomized low-rank approximation; kernel matrices

Does there exist a universal constant $C\geq1$ such that, for every
$n\geq1$, every Hermitian positive-semidefinite $A\in\mathbb C^{n\times n}$,
every integer $1\leq r\leq n$, and every $0<\varepsilon<1$, RPCholesky
satisfies

$$
\mathbb E\operatorname{tr}(R_k)\leq(1+\varepsilon)\tau_r(A),
\qquad k=\min\{n,\lceil Cr/\varepsilon\rceil\}?
$$

The expectation is over the algorithm's adaptive pivots. The constant must
be independent of dimension, spectrum, rank, and tolerance. The target
concerns this fixed pivoting rule.

**References:** Epperly, [*A new analysis of the randomly pivoted Cholesky
algorithm*](https://arxiv.org/html/2608.20633v1), §1.2, conjecture immediately
after Eq. (1.5), and Corollary 1.3. Earlier motivation appears in
Epperly, [*Make the Most of What You Have*](https://tropp.caltech.edu/dissertations/Epp25-Making-Most.pdf),
Caltech dissertation (2025), §11.1, p. 181.

**Status check:** The August 2026 paper proves the larger bound
$k\geq r/\varepsilon+2r\sqrt{\log r}+r\log(1/\varepsilon)+2.3r$
and explicitly conjectures the displayed improvement. Searches for the
paper's title, `RPCholesky optimal r epsilon`, and `RPCholesky conjecture`
found no subsequent resolution. The arXiv record listed only v1, posted
August 21, 2026. The weaker dissertation Conjecture 11.1 is therefore
excluded as resolved by this later preprint.

<a id="ra-02"></a>

## RA-02 — Polynomial trace-error factor after exactly the target rank of pivots

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** randomized factorization; approximation guarantees

Do constants $C>0$ and $p\geq0$ exist such that, for every $n\geq1$,
every Hermitian positive-semidefinite $A\in\mathbb C^{n\times n}$, and
every integer $1\leq r\leq n$,

$$
\mathbb E\operatorname{tr}(R_r)\leq Cr^p\tau_r(A)?
$$

Both constants must be independent of $n,r,A$. Exactly $r$ RPCholesky
steps are permitted, with the zero-residual convention above. This asks
for a polynomial approximation factor without oversampling; RA-01 instead
allows additional pivots to obtain relative error near one.

**References:** Epperly, [*Make the Most of What You Have*](https://tropp.caltech.edu/dissertations/Epp25-Making-Most.pdf),
§11.1, Conjecture 11.2, p. 182; Chen et al.,
[RPCholesky](https://doi.org/10.1002/cpa.22234), Lemma 5.5, p. 1020.
Gilles and Wilber, [*Low-Rank Approximation by Randomly Pivoted LU*](https://arxiv.org/html/2601.22344v1),
§3.1, paragraph following Theorem 3, explicitly reiterate this conjecture.

**Source normalization:** The dissertation calls $A^{(r)}$ a residual but
prints $\operatorname{tr}(A-A^{(r)})$, without expectation. We use its
cited Lemma 5.5 to correct both notation defects. The later paper confirms
the intended polynomial improvement over that lemma's $2^r$ factor.

**Status check:** Searches for `RPCholesky r-step polynomial`,
`RPCholesky conjecture polynomial`, and the cited papers found no resolution.
Epperly's August 2026 oversampling theorem does not supply a polynomial
factor at exactly $r$ steps. Its Theorem 1.2 is noninformative at $k=r$.

<a id="ra-03"></a>

## RA-03 — Improve the randomized LU squared-error factor to $2^k$

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Topic:** randomized LU; low-rank approximation

For $A\in\mathbb C^{m\times n}$, define exact-arithmetic residuals
$S_0=A$. At step $t$, choose $(i,j)$ with conditional probability
$|(S_t)_{ij}|^2/\|S_t\|_F^2$ and update

$$
S_{t+1}=S_t-\frac{S_t(:,j)S_t(i,:)}{(S_t)_{ij}}.
$$

After a zero residual, keep subsequent residuals zero. Prove or refute,
for every $m,n\geq1$, every $A$, and every
$1\leq k\leq\min(m,n)$,

$$
\mathbb E\|S_k\|_F^2\leq2^k
\sum_{j>k}\sigma_j(A)^2,
$$

where singular values decrease with $j$. The bound concerns the mean
squared Frobenius error of this specified algorithm.

**References:** Gilles and Wilber, [*Low-Rank Approximation by Randomly
Pivoted LU*](https://arxiv.org/html/2601.22344v1), Algorithm 1 and §3.1,
Theorem 3, Eq. (10), and the following conjecture (pp. 7–8).

**Status check:** Their theorem gives $4^k$; the conjecture explicitly
replaces it by $2^k$. Searches for the title, `randomly pivoted LU 2^k`,
and improved RPLU error bounds found no later resolution. The arXiv
submission history listed only v1 of January 29, 2026. The August 2026
RPCholesky theorem addresses a different pivot distribution and norm.

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
