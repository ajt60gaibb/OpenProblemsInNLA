# Proof audit — continuation 5

## Completion status

The full RA-14 characterization remains **PARTIAL**. The new manuscript claims a proof of a universal lower bound, not a proof that this lower bound is everywhere optimal. A concrete remaining transition appears in Section 11. The mathematical arguments have not been independently peer reviewed or formalized in a proof assistant.

## 1. Model and quantifiers

The unknown input is any real square matrix. Both oracle directions cost one query per vector. Queries and outputs are measurable, may be randomized, and may depend on every preceding reply. The success requirement is pointwise in the input, with probability at least 0.99. All computations other than oracle calls are free in the exact-real model.

The new hard inputs are symmetric. A two-sided algorithm on those inputs has no extra oracle information: multiplication by the transpose is the same multiplication. Queries are orthogonalized against the previously queried span using products already known by linearity. Output directions are appended and charged, rather than treated as free observations. A padded procedure is used only when its deterministic padded budget is at most the ambient dimension.

## 2. Rank necessity

The `q >= k` fallback is proved using a nonsymmetric rank-k Gaussian input. A random orthogonal projector would be insufficient when k is close to n, because its small complementary subspace could be learned instead. The conditional rectangular Gaussian block handles both query directions. The proof does not depend on a one-sided restriction.

## 3. Hard distribution

Let `r=n-k`. Under the base law, `H=X X.T` for standard Gaussian `X` of size `n by r`. Define `pdet` as the product of strictly positive eigenvalues. For an integer `nu >= 0`, tilt the base probability density by `pdet(H)^(nu/2)`.

The normalizing integral is finite: the exponent is nonnegative and Gaussian Gram determinants have all positive moments. The law has an exact k-dimensional kernel, uniformly oriented. Its nonzero eigenvalues equal those of a Gaussian `r by (n+nu)` Gram matrix. Section 3 derives the Gaussian Gram density from Gram–Schmidt and its Jacobian instead of appealing to a vaguely specified random-matrix model.

The actual RA-14 input in the high-accuracy argument is `M=I-H/(100n)`. The scale `100n` is fixed and known; it is not an unknown norm evaluated for free. Each M-product and H-product simulates the other at one oracle call. No inverse-matrix oracle is used.

## 4. Adaptive Schur completion

For `t<r` orthonormal adaptive queries, write the conditional matrix as

```text
H = [[J, B.T], [B, B J^{-1} B.T + S]],
S = Y Y.T,
Y of size (n-t) by (r-t).
```

Under the base law, the remaining Gaussian matrix is independent of the transcript. The proof conditions on the transcript before each next query, rotates only the unobserved Gaussian block, and then reveals one row and column. It therefore does not replace an adaptive direction by a fixed unconditional direction.

The queried compression J is positive definite almost surely until `t=r`. The tilted law is absolutely continuous with respect to the base law, so this nonsingularity remains true. The law of S under the tilt is then computed explicitly, not assumed to remain standard Wishart.

## 5. Pseudodeterminant and exact posterior

With Q spanning the kernel of S, define

```text
K = B J^{-2} B.T,
C = Q.T K Q,
U = [-J^{-1}B.T Q; Q] (I+C)^{-1/2}.
```

The required identity is

```text
pdet(H) = det(J) pdet(S) det(I+C).
```

It is proved by comparing the first nonzero coefficient in `det(H+zI)` under a block-triangular congruence. An ordinary determinant identity would give zero on both sides and would not suffice here.

The factorization shows that, conditional on the actual adaptive transcript, the kernel density relative to uniform Grassmann measure is exactly

```text
weight(Q) proportional to det(I+Q.T K Q)^(nu/2).
```

The positive eigenvalues of S and its kernel orientation remain independent after their separate density factors are applied. This follows by conditional change of measure on the full input distribution, not by assuming a nonadaptive query schedule.

An additional untilted identity gives the expected logarithm of the complementary kernel overlap as a telescoping sum of digamma differences. It is a useful check, but the main lower bound does not use it.

## 6. Grassmann integration lemma: main review point

For `d>k+1`, `K>=0`, `nu>=0`, `beta>0`, and the preceding angular density, the manuscript proves

```text
E[Q (I+beta Q.T K Q)^{-1} Q.T]
    <= ((k+nu/beta)/(d-k-1)) I.
```

The proof uses a globally defined horizontal vector field

```text
X(Q)=(I-Q Q.T) v v.T Q (I+beta Q.T K Q)^{-1}.
```

Initially v is an eigenvector of K. In a local graph chart, the uniform volume density has zero first derivative at the chart origin by reflection symmetry. The manuscript differentiates the chart vector field and its weight explicitly. Integrating the weighted divergence over the compact Grassmann manifold gives the stationarity identity.

The score term is bounded using `K-kappa*v*v.T >= 0`, hence `kappa*a*a.T <= C` in compressed coordinates. In particular, the proof does not assert that unrelated compressed matrices commute. The inverse functions of C do commute with C. The case `kappa=0` is handled separately without an inverse of a singular matrix.

Finally, invariance under eigenbasis sign changes makes the expected matrix diagonal in that basis. This is essential: inequalities for eigenvector directions alone would not justify the bound for an arbitrary adaptive next direction without this step.

The new tests check the local divergence and score by finite differences, pointwise inequalities, and special cases. They are not a proof of the integration-by-parts identity or its universal inequality. This lemma and the posterior derivation are the two highest-priority parts for independent review.

## 7. One-query information budget

For any fixed full-kernel basis U0, set

```text
Phi_t = log det(I + alpha U0.T P_{V_t} U0), alpha=nu/k.
```

The exact rank-one update is

```text
Phi_(t+1)-Phi_t
 = log(1 + alpha*v.T Q (I+(1+alpha)C)^{-1} Q.T v).
```

The next query v is predictable from the transcript. The new reply is not needed to determine this overlap increment. Applying the posterior lemma with `beta=1+alpha`, then `log(1+u)<=u`, gives conditional growth at most `2nu/(n-t-k-1)`.

For `n>=8`, `k<=n/8`, `T<=n/4`, summing conditional expectations gives

```text
E[Phi_T] <= 4nu*T/n.
```

This is an expectation bound, not a bound on every realized path. The diagnostics compare empirical means with it; all path rows are retained. The proof holds for every fixed algorithmic seed and then integrates over the independent seed.

## 8. Constant-accuracy fallback

The proof uses `nu=4095n`, so the nonzero spectrum has `4096n` Gaussian degrees of freedom. A direct chi-squared tail and sphere-net argument confines `H/(4096n)` to `[3/4,5/4]` on its range with sufficiently high probability. On a successful run for `M=I-H/(4096n)`, the output captures at least `55/64` of every hidden kernel direction.

The same potential argument then proves `q >= 2^-20*k*log(en/k)`. Its constant is weaker than the earlier v4 constant. It is included to make the new global proof independent of v4's information-theoretic lower-bound machinery. The small-logarithm branch uses `q>=k`; no dimension-growth condition is dropped.

## 9. Exact imported spectral dependency

The only imported non-elementary probabilistic theorem in the new lower argument is Rudelson–Vershynin (2009), Theorem 1.1, specialized to a real standard Gaussian `N by r` matrix:

```text
P[s_min(G) <= t*(sqrt(N)-sqrt(r-1))]
 <= (C_RV*t)^(N-r+1) + exp(-c_RV*N).
```

It applies for every fixed `N>=r` and `t>0`. Here `N=n+nu`, `r=n-k`. No assumption that the aspect ratio stays bounded away from one is imposed.

Set `t_*=[2 max(C_RV,1)]^-1` and `a=t_*^2/900`. Fixed constants `n_*` and `nu_*` make the failure probability at most 0.005; a separate Gaussian norm bound accounts for another 0.005. On the resulting event,

```text
||H|| <= 100n,
lambda_min_positive(H) >= 100a*(nu+k)^2/n.
```

Thus `M=I-H/(100n)` has exact leading eigenvalues one and tail in `[0,1-g0]`, with `g0=a*((nu+k)/n)^2`. No deformed-Wigner outlier-location estimate or dimension threshold is imported into this argument. The external theorem itself is not re-proved or numerically certified.

## 10. Residual-to-kernel bridge and query overhead

A good spectral residual is not, by itself, a nearly optimal PCA trace. Appendix A reproduces the earlier warm-start proof, including its weighted graph inequality, Fejer-type polynomial, noncommuting trace bound, and the final Ritz extraction.

With `e=g0/4`, successful RA-14 output at `epsilon<=e` is a valid warm start. At most

```text
k ceil(10/sqrt(e)) <= D*n*k/(nu+k)+k, D=20/sqrt(a)
```

additional queries give kernel trace at least `799k/800`. Another at most k queries includes that output in the query span. All of them are charged. There is no free `M*Z` or free compression matrix.

Concavity gives `Phi_T >= (799/800)*k*log(1+nu/k)` on the joint good event. Only the trace is required: the proof does not incorrectly infer a lower bound on every principal angle from a trace bound.

Proposition 9.3 keeps the query overhead visible:

```text
q >= (n*k/(5nu))*log(1+nu/k) - D*n*k/(nu+k) - 2k,
```

under its stated spectral and accuracy hypotheses. The right side can be negative. The subsequent global result does not ignore this subtraction.

## 11. Universal constants and exhaustive parameter split

Choose once and for all

```text
B_*=2/sqrt(a), D=20/sqrt(a),
R >= max(nu_*, B_*, 2), log(R) >= 100(D+1).
```

R may be extremely large, but is independent of n, k, and epsilon.

The proof first handles `n<n_*`, `k>=n/(8R)`, and `sqrt(epsilon)>=1/(8B_*)` using the rank or constant-accuracy lower bounds. In the remaining regime choose

```text
nu=ceil(max(R*k, B_*n*sqrt(epsilon))).
```

Every needed finite condition is then checked: `nu_*<=nu<=n/4`, `k<=n/8`, and `e>=epsilon`. Under the supposed low query budget, the postprocessing overhead is at most one hundredth of `G_nu=(nk/nu)log(1+nu/k)`, and the padded total is below `n/50`. The potential upper and lower expectations contradict each other.

The final comparison uses the decreasing function `log(1+u)/u`. It is made separately according to whether `B_*n*sqrt(epsilon)/k` exceeds R. The proof displays a positive minimum of five universal constants. This verifies an all-parameter lower bound by a new construction and fallbacks; it does not append an n-cap to a previously restricted lower bound.

## 12. Upper bound audit

Appendix B reproduces the previously developed exact-real upper bound, rather than importing it from an unspecified algorithm. It retains both Gaussian sketches, a charged estimate of the unknown `sigma_{k+1}^2`, the exact rank-deficient branch, and the cost of all compressed products.

The polynomial surrogate can be indefinite. Its extraction therefore uses right singular vectors of the compressed operator, not algebraic Ritz vectors substituted without justification. A scalar polynomial majorant transfers the surrogate residual to the desired residual. The exact n-column recovery branch handles the high-cost regime. The logarithm is reduced to `log(en/k)` only in the branch where this parameter comparison is valid.

## 13. What the package does not establish

Neither of these all-parameter equalities is proved:

```text
q_sp = Theta(min(n, k/sqrt(epsilon)*log(en/k)))
q_sp = Theta(k/sqrt(epsilon)*log(1+n*sqrt(epsilon)/k)).
```

At `k=1`, `epsilon=(log(n)/n)^2`, the current lower scale is `n log(log n)/log n` while the upper scale is n. This is an unbounded gap. The potential budget, the finite-dimensional spectral theorem, and the existing upper algorithm do not remove it.

Experiments, deterministic Krylov lower bounds, visible-block direct sums, and exact n-query recovery do not supply the missing all-adaptive lower bound or a sharper universally valid algorithm. The full problem remains PARTIAL.
