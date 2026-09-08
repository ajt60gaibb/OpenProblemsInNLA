# Sparse solvers and eigenvalue algorithms

The status checks in this chapter were performed on **2026-09-08**, including
the August 21 version of the Simons workshop report. No resolution found means
that the bounded searches described below found none. Ratings are editorial.
All norms are Euclidean vector norms or their induced matrix norms.

<a id="ke-01"></a>

## KE-01 — Exploit spectral outliers without losing input sparsity

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** sparse linear systems; randomized preconditioning

Let $A\in\mathbb R^{n\times n}$ be nonsingular, with singular values
$\sigma_1\geq\cdots\geq\sigma_n>0$, and write $N=\operatorname{nnz}(A)$
and $\kappa_2(A)=\sigma_1/\sigma_n$.
The input consists of its nonzero entries and their indices, $b\ne0$,
$\varepsilon\in(0,1/2)$, $k\in\{0,\ldots,n-1\}$, and $\kappa\geq1$, with the promise
$\sigma_{k+1}/\sigma_n\leq\kappa$. Fix any exponent $\omega_0>2$ for which
square matrix multiplication has an $O(m^{\omega_0})$ arithmetic algorithm.

Does a randomized algorithm exist that, for every such input, produces
$\widehat x$ satisfying

$$
\|A\widehat x-b\|_2\leq\varepsilon\|b\|_2
$$

with probability at least $0.99$, using at most

$$
C\bigl(k^{\omega_0}+N\kappa\bigr)
\bigl[1+\log(n\kappa_2(A)/\varepsilon)\bigr]^q
$$

exact arithmetic operations? Here $C,q$ may depend on the chosen multiplication
algorithm, but not on the input. Direct entry access is allowed. The display
makes the workshop's suppressed logarithms and accuracy convention explicit;
$\omega_0$ avoids assuming that the infimum defining the multiplication
exponent is attained.

**References:** Amsel et al., [*Linear Systems and Eigenvalue Problems*](https://arxiv.org/html/2602.05394v3#S2.SS4),
Definition 2.4 and Problem 2.5. Dereziński and Sidford,
[*Approaching Optimality for Solving Dense Linear Systems with Low-Rank Structure*](https://doi.org/10.1137/1.9781611978971.37),
SODA 2026, pp. 925–938; [full manuscript](https://arxiv.org/html/2507.11724),
Theorems 3 and 29, gives the dense-input predecessor.

**Status check:** Searches for `sparse outlying singular values solver 2026`
and `spectral outliers linear systems 2026` found the newer Liu, Nguyen, Peng,
and Yang [*Faster Solvers for Sparse Systems with Large Spectral Outliers*](https://yangpliu.github.io/pdf/faster-solvers-sparse-spectral-outliers.pdf).
Its Theorem 1.1 assumes an explicitly given factor $B$ in $B^TBx=b$, bounded
spectral tail, polynomial conditioning, and short rational input. For an
$m\times d$ factor with at most $s$ nonzeros per row, its bit bound includes
$m^{o(1)}\widetilde O(ms+\sqrt{d/k}\,k^2+k^{\omega+\eta})$. These input
restrictions and extra terms do not establish the requested general bound.
The workshop's August update records this as partial progress on Problem 2.9.

<a id="ke-02"></a>

## KE-02 — Construct a separating diagonal perturbation in nearly linear time

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** Hermitian eigenproblems; deterministic regularization

For a Hermitian matrix $H$ with eigenvalues listed with multiplicity, define

$$
\operatorname{gap}(H)=\min_{i\ne j}|\lambda_i(H)-\lambda_j(H)|.
$$

Do universal constants $a,c_0,C,q>0$ and a deterministic algorithm exist with
the following property? For every $n\geq2$, Hermitian tridiagonal
$T\in\mathbb C^{n\times n}$ with $\|T\|_2\leq1$, and
$\delta\in(0,1/2)$, the algorithm receives the three diagonals and returns
a real diagonal matrix $D$ such that

$$
\|D\|_2\leq\delta,
\qquad
\operatorname{gap}(T+D)\geq c_0(\delta/n)^a,
$$

using at most $Cn[1+\log(n/\delta)]^q$ exact arithmetic operations and
comparisons? Square roots of nonnegative real numbers are allowed at unit
cost; extracting bits from exact real inputs is not.

This selects the explicitly proposed nearly linear version of the
deterministic Minami problem. It preserves tridiagonal structure and requires
only the perturbation as output. Its diagonal restriction and cost target
make it distinct from the general, cubic-cost regularization question IE-07.

**References:** Amsel et al., [workshop report](https://arxiv.org/html/2602.05394v3#S3.SS1),
Problem 3.2. Sobczyk, [*Deterministic complexity analysis of Hermitian eigenproblems*](https://arxiv.org/html/2410.21550v2),
§1.1 for the arithmetic model, Theorem 1.1 for the tridiagonal eigensolver,
and §5, question 4, for deterministic spectral separation.

**Status check:** Searches for `deterministic Minami perturbation`,
`Minami deterministic eigenvalue gap algorithm 2026`, and `Minami
derandomization matrix` found no construction meeting this bound. Sobczyk's
April 2025 revision gives a deterministic full tridiagonal diagonalization in
nearly quadratic time; it does not provide the requested nearly linear
diagonal perturbation. The workshop retains Problem 3.2 in its August 2026
update. The normalization and a bounded perturbation are stated explicitly
here, making the scale of its gap guarantee unambiguous.

<a id="ke-03"></a>

## KE-03 — Find a near-largest nonnormal eigenvalue using few matrix-vector products

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** nonsymmetric eigenvalue computation; query complexity

An unknown diagonalizable $A\in\mathbb C^{n\times n}$ is available only
through exact queries $v\mapsto Av$. A number $K\geq1$ is supplied, with
the promise that $A=V\Lambda V^{-1}$ for some diagonal $\Lambda$ and
$\|V\|_2\|V^{-1}\|_2\leq K$. Assume
$\rho(A)=\max_{\mu\in\sigma(A)}|\mu|>0$; neither the eigenvalues nor $V$
are supplied.

Do universal constants $C,a,b>0$ and a randomized algorithm exist that,
for every such input and every $\varepsilon\in(0,1/2)$, returns a complex
number $z$ with probability at least $0.99$ such that

$$
\text{there exists }\mu\in\sigma(A):
\quad |\mu|\geq(1-\varepsilon)\rho(A),
\qquad |z-\mu|\leq\varepsilon\rho(A),
$$

using at most $C[1+\log(nK)]^a\varepsilon^{-b}$ matrix-vector queries?
The algorithm may perform finite exact arithmetic between queries; the
requested bound concerns query count. Products with $A^*$ and solutions of
shifted linear systems are not additional oracle operations. Supplying $K$
and fixing a success probability make the computational formulation explicit.

**References:** Amsel et al., [workshop report](https://arxiv.org/html/2602.05394v3#S3.SS5),
Problem 3.9. Shah, Srivastava, and Zeng,
[*Sparse Pseudospectral Shattering*, first version](https://arxiv.org/pdf/2411.19926v1),
§1.3, Theorem 1.5 and its power-iteration argument, supplies the related
spectral-radius estimate cited by the workshop.

**Status check:** Searches for `nonnormal eigenvalue query complexity 2026`
and `nonnormal spectral radius matrix-vector algorithm 2026` found no
resolution. The radius estimate controls a nonnegative scalar and allows
backward error; it does not locate a near-extremal eigenvalue in the complex
plane as required here. The [April 2026 third version](https://arxiv.org/abs/2411.19926v3)
replaces that application with a GMRES application (§6), so the version-specific
locator above is intentional. The workshop still poses Problem 3.9 in its
August update, separately from its resolved general Ritz-compression question.

## Additional leads — uncounted

- **Algebraic multigrid, workshop Problem 2.3:** the target approximate inverse
  is precise, but the report does not specify which multigrid hierarchy,
  smoother, or construction algorithm is to satisfy it. Replacing the method
  requirement by an unrestricted approximate-inverse algorithm risks changing
  the question; no entry is admitted from that replacement.
- **Finite-precision CG, workshop Problems 2.15–2.19:** the n-step precision
  question is promising, but a sharp formulation needs fixed recurrences,
  rounding and breakdown conventions, and input conditioning assumptions.
  The broad comparison and block-analysis requests are not additional entries.
- **SVD without condition-number dependence:** Sobczyk's §5, question 2,
  explicitly asks to remove the dependence in Theorem 1.2. That theorem gives
  both an exact factorization with approximate isometries and a weaker
  backward-approximation consequence. The intended retained accuracy guarantee
  needs clarification before this is admitted as a general algorithm-existence
  question. Searches for `Sobczyk SVD condition number` and `deterministic SVD
  condition 2026 complexity` found no later general resolution.
