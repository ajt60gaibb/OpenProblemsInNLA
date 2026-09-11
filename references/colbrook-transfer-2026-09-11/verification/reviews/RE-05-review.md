# Independent review: RE-05

**Verdict: PASS for the complete canonical RE-05 existence question.** The original linear-family theorem, spectral profiles, centered-error analysis, and affine confidence amplification are sound. The auxiliary constrained-convex success proof is also sound; an off-event algorithm-definition qualification was identified and has been explicitly repaired in the separately preserved reviewed source. The repaired auxiliary statement passes. Prior-work attribution and access limits remain separate from proof validity.

Review date: 2026-09-11. Reviewer task: `/root/review_transfer_volume_learning`. This is an independent Codex subagent proof audit, not human peer review or a priority certification. The complete original source and common preamble were read, followed by a complete-source diff of the revision. The canonical README and generated problem TeX were both checked. The supplied verification programs were not used as a substitute for the derivations below.

## Artifact identity

Hash convention: complete UTF-8 text, CRLF replaced by LF, UTF-8 encoding, SHA-256. No trimming or other whitespace normalization; final newline is retained.

| Artifact | Normalized bytes | Normalized SHA-256 |
| --- | ---: | --- |
| `.cache/colbrook-transfer-submission/nla_submission/manuscripts/05_linear_family_relative_sketch.tex` | 15928 | `2b64b6826cad9695f8a581e26573efd55799d3e701d52b1b37f10c84e921818b` |
| `references/colbrook-transfer-2026-09-11/reviewed-sources/05_linear_family_relative_sketch.tex` | 16219 | `c648f71278eb5b60b59a9e5fa837ecd623e25d918a05ff3ad54ad245ae4f0eee` |
| `.cache/colbrook-transfer-submission/nla_submission/manuscripts/common_preamble.tex` | 1105 | `8b784fe6ac56151b19d51534474560bf45df7b278015cd0c834569e2550fada4` |

The sole mathematical-text change in the reviewed source is a guard before constrained convex optimization: report failure when `C` does not dominate `I_q/2`; otherwise solve the coercive quadratic on the closed convex set. The linear-family and amplification arguments are unchanged. The original is preserved separately. The common preamble has ordinary notation definitions and adds no unstated assumptions.

## Exact canonical target coverage

Canonical target: `randomized-and-low-rank-approximation/RE-05/README.md` and `problem.tex` as read on the review date. It asks for a uniform randomized algorithm for every explicit independent basis of an arbitrary square q-dimensional real matrix family, with two-sided exact vector queries, norm-relative error `1+epsilon`, success at least 0.99, and a bound of the displayed `C sqrt(q) epsilon^(-a)` times a polylogarithm, for fixed nonnegative integers a and b. The canonical model explicitly permits Gaussian sampling and exact SVD primitives.

The manuscript handles rectangular matrices, hence square ones. Frobenius orthonormalization of the explicit independent input basis requires no access to A. Keeping that invertible coordinate transformation lets the algorithm output coefficients in the original basis. Its sole accesses to A are exactly r left products and s right products. Each block column is charged individually. The spectral split and all random directions depend on the given family and randomness only, before any response. These are legal nonadaptive queries in the more permissive canonical model.

The theorem alone has success 0.9, so amplification is essential to the exact target. Set the desired squared excess to the canonical epsilon, take 15 independent copies with internal squared parameter `epsilon/9`, and use the proved median-radius selector. Then failure is at most `exp(-0.32*15)=0.00822974704902003 < 0.01`, and the final norm factor `sqrt(1+epsilon)` is at most `1+epsilon`. The resulting query upper bound is

```text
15 [ 2 sqrt(q(16 log(20q)+1440/epsilon)) + 8 log(20q) + 1 ].
```

For `q>=1` and `0<epsilon<1/2`, this is of the canonical form, for example with integers `a=b=1` and a sufficiently large absolute C. Both the constant and the algorithm are uniform over basis, target, and ambient dimension. The idealized arithmetic and exact SVD requirements agree with the canonical model; no bit-complexity or floating-point stability theorem follows.

The source's Section 5 does explicitly pose the general pure-relative linear-family question, separately from its finite-family question and additive-error corollary. The canonical match therefore does not rely on a finite-family discretization. [Amsel et al., arXiv:2507.19290v2, Section 5](https://arxiv.org/html/2507.19290v2)

## Proof audit: deterministic split and Gram matrix

Orthonormality gives `tr R=q`. Orthogonal change of Frobenius basis leaves `sum_i P_i P_i^T` unchanged by contracting the two coefficient indices. Every selected eigenvalue exceeds t, so `r t <= q`; the stated weak bound `r <= q/t` is valid. Projection onto the complementary eigenspaces gives `sum_i T_i T_i^T <= t I_m`.

H is the Gram matrix of projected basis elements and K is the Gram matrix of their exact left parts. Both are positive semidefinite, and `H+K=I_q`. In particular `H<=I_q`. The responses determine `U^T A` and `(I-Pi)Ag_j`, so the entire least-squares objective and its q-dimensional design are observable. No norm estimate, residual oracle, or hidden access to A appears.

With `X=K+M^T M`, one has `X>=0`, `E X=I`, and `X-I=M^T M-H`. The mean identity depends on retaining the original orthonormal coefficient coordinates, as the manuscript stresses. Reorthonormalizing the projected family without transforming the deterministic part would be an error, but the proof does not do this.

### Gaussian second moment

For `T=sum_i a_i T_i`, the l-th component of `(M^T M-H)a` is the centered quadratic form with matrix `T_l^T T`. A direct fourth-moment expansion yields the variance sum written in the manuscript. Transposing inside the traces, if needed, gives exactly

```text
sum_l [ tr((T^T T_l)^2) + tr(T^T T_l T_l^T T) ].
```

For nonsymmetric real Z, `tr(Z^2)` need not be nonnegative, but `tr(Z^2)<=||Z||_F^2` by entrywise Cauchy-Schwarz. The second summand is already `||T^T T_l||_F^2`. Summing and cyclically moving factors gives `2 tr(T^T (sum_l T_l T_l^T) T) <= 2t ||T||_F^2 <= 2t ||a||_2^2`. Thus the asserted Loewner bound follows for every a. Finally `E X^2=I+E(X-I)^2`, so the second moment is bounded by `(1+2t)I`. No commutation assumption on H and an individual random Gram matrix is used.

### Matrix lower tail, including noncommutativity

The scalar inequality `exp(-theta x)<=1-theta x+theta^2 x^2/2` holds for all nonnegative x, so functional calculus and expectation give a scalar upper bound on `E exp(-theta X_j)`. The hypotheses also imply `v>=1` because `E(X_j-I)^2>=0`, so the quadratic scalar bound is positive. Using `1+u<=exp(u)` is legitimate.

Let the partial sum before the final draw be S. Golden-Thompson gives

```text
tr exp(-theta(S+X_j)) <= tr[exp(-theta S) exp(-theta X_j)].
```

Independence lets one condition on S. The second factor's expectation is bounded by a scalar multiple of I. Trace multiplication by the positive matrix `exp(-theta S)` preserves that inequality. This proves the one-step recursion; iterating it does not assert a false multivariate Golden-Thompson product inequality. This scalar-bound structure is precisely what makes the elementary iteration valid for noncommuting summands.

On the bad lower-eigenvalue event the trace exponential is at least `exp(-theta s/2)`. Markov then gives `q exp(s(-theta/2+theta^2 v/2))`; inserting `theta=1/(2v)` produces exactly `q exp(-s/(8v))`. Gaussian summands are unbounded above, but their negative exponentials are bounded and their second moments are finite. No upper-tail boundedness premise is missing. The cited matrix-Laplace framework is consistent with this argument. [Tropp, User-friendly tail bounds for sums of random matrices](https://arxiv.org/abs/1004.4389)

### Centered regression and the main probability bound

At the Frobenius projection, the deterministic normal offset and expected random offset sum to zero. For the random portion, direct expansion of a nonsymmetric Gaussian quadratic form gives `Var(g^T Z g)=tr(Z^2)+tr(ZZ^T)<=2||Z||_F^2`. The independent averaging contributes `1/s`. The sum over basis elements is bounded by the same residual leverage matrix, giving `E||z||^2 <= 2t ||E||_F^2/s`. Cross-coordinate independence is not needed: the squared vector norm is the sum of its coordinate squares.

On `C>=I/2`, the normal equations yield `d=C^(-1)z` and `||d||^2<=4||z||^2`. Markov bounds the joint event of excessive coefficient error and good Gram matrix by `8t/(s epsilon)`. The Gram event has failure at most 1/20 when `s>=8(1+2t)log(20q)`, and the offset event has failure at most 1/20 when `s>=160t/epsilon`. A union bound suffices; no independence between these events is claimed. Orthogonality makes the population error exactly `||E||^2+||d||^2`.

When the optimal residual is zero, z vanishes identically and positive Gram definiteness ensures exact recovery. No division by a zero residual occurs. Ordinary linear least squares always has a minimizer even on a singular design, and the specified minimum-coefficient-norm rule makes the main algorithm defined there.

The choice `t=sqrt(q/L_0)` and ceiling for s meets both lower bounds. Adding `q/t` to the ceiling gives the stated query estimate. The alternative split after r eigenvectors has exactly the stated residual eigenvalue, including ties; the exact-support branch with zero residual leverage uses no random queries. Transposition exchanges the two allowed oracle orientations. Choosing the better plan uses only the family.

## Affine confidence amplification

Subtracting the known affine offset from each oracle response is valid without an extra query. Differences of coefficient vectors in the orthonormal direction basis equal Frobenius differences of the corresponding matrices. If a strict majority of candidates lie within rho of the true projection, each successful candidate has median radius at most `2rho`. The selected candidate's median ball contains a strict majority and therefore intersects the successful majority. Its distance to the truth is at most `3rho`. This reasoning includes zero self-distance, ties, and `rho=0`.

Taking internal parameter `epsilon/9` yields the desired final squared coefficient error. Independent copies each succeed with probability at least 0.9 for every fixed input. Hoeffding bounds the chance of at most half successes by `exp(-0.32 L)`. Pairwise coefficient distances require no additional target queries or knowledge of the optimum. Reusing identical exact left responses would also be possible, but charging every copy as in the canonical reduction above is a valid conservative bound.

## Closed-convex extension and reviewed repair

Population projection onto a nonempty closed convex subset of a finite-dimensional affine space exists and is unique. With `e_i=<P_i,E>`, its variational inequality is `e^T d<=0`. Centering the sketched normal offset by subtracting e leaves exactly the same variance calculation for arbitrary residual E.

The sketched first-order condition tested against the population optimizer gives `d^T C d <= (e+z)^T d`. On the good Gram event this implies `||d||<=2||z||`. More importantly, the population excess satisfies

```text
||d||^2 - 2e^T d
<= ||d||^2 - 2d^T C d + 2z^T d
<= 2z^T d <= 4||z||^2.
```

This sign-sensitive inequality is correct. It is stronger than a distance-only conclusion and proves the stated constant-success bound by the same Markov and Gram estimates, including exact recovery when E=0.

The original instructs minimization on K without an explicit failure branch. For a singular quadratic, closedness alone does not imply attainment: for example the closed convex set `{(x,y): x>0, y>=1/x}` has unattained infimum zero for objective `x^2`. This is not a counterexample to the success proof. Under the theorem's sample bound, a positive-definite Gram event has positive probability; since `det C` is a polynomial in continuously distributed Gaussian coordinates, singularity actually has probability zero. Nevertheless, an explicitly total algorithm should say what happens there.

The reviewed source now tests `C>=I/2` and reports failure otherwise, before constrained optimization. On the accepted event the quadratic is coercive on the containing affine space, so it attains a unique minimum on K. This precise repair requires no additional queries, and its reported failures are already in the theorem's failure bound. The reviewer checked the sole changed paragraph against the original and recomputed the full revised hash above. The optimization remains conditional on being able to solve the supplied convex problem; polynomial-time optimization for arbitrary descriptions of K is not claimed.

The manuscript correctly declines to extend the median-radius argument to general convex constraints: the normal term `-2e^T d` can be positive, so proximity alone is insufficient to upper-bound excess. This limitation does not affect canonical RE-05, which is a linear-family question.

## Independent exact diagnostic

A fresh Python standard-library diagnostic, independent of the supplied scripts, used the integer matrices

```text
T1 = [[ 1, 2, 0], [-1, 1, 3]]
T2 = [[ 0, 1,-2], [ 2, 0, 1]]
T3 = [[ 1,-1, 1], [ 0, 2,-1]]
```

It directly enumerated all Gaussian fourth-moment index contractions `E[g_i g_j g_k g_l]` rather than substituting the claimed trace formula. Every entry of the full centered Gram second moment matched the independently assembled trace expression, producing

```text
[[ 431,  118, -102],
 [ 118,  263, -178],
 [-102, -178,  264]].
```

It also checked the directional reduction for coefficients `(1,0,0)`, `(1,-2,3)`, and `(2,1,-1)`, and the offset variance and its upper bound for all three nonsymmetric matrices `T_i^T E`, with `E=[[1,2,3],[-2,1,0]]`. All exact integer checks passed. These examples test the algebra only; the universal Loewner and probability arguments are established above. An initial attempt to use SymPy failed because that module was unavailable; the executed successful diagnostic uses only the standard library.

## Prior-work check and limits

On 2026-09-11 the current raw `main.tex` and `supplement.tex` were accessible. The original draft's claim that the full prior manuscript was unavailable is therefore a historical access limitation, not the present review's limitation.

The current prior main source uses the same exact high-leverage/ Gaussian-complement least-squares algorithm, second-moment mechanism, zero-leverage branch, and median selector. Its profile contains a squared logarithm. Its covariance argument controls both tails via Schatten moments and an expected-norm inequality, while its discussion explicitly suggests a sharper lower-tail argument as a possible route to reducing logarithms. The submitted lower-tail proof is a valid different route for the same estimator; this observation establishes no priority or exhaustive novelty claim. [Current prior main source](https://raw.githubusercontent.com/andotheror/matvec-structured-matrix-approx/main/main.tex)

The relevant full proofs in the prior supplement, Appendix A and Appendix B, were inspected for covariance, offset centering, exact support, and amplification. They contain the same fourth-moment and median geometry ingredients. The prior's separate lower bounds and statistical consequences are outside this manuscript's claims and are not certified by this review. [Current prior supplement](https://raw.githubusercontent.com/andotheror/matvec-structured-matrix-approx/main/supplement.tex)

The repository lists original-version PDFs with `2026-07-30` filenames and associated timestamp-proof filenames. Those displayed filenames are evidence of the repository's announcement, not an independently authenticated first-publication date. The account name `andotheror` is not verified personal identity; a name displayed in source metadata is also not independent identity verification. [Prior repository](https://github.com/andotheror/matvec-structured-matrix-approx)

Direct attempts to retrieve the displayed [Zenodo record 21698599](https://zenodo.org/records/21698599), its DOI resolver, and its API record failed in the browsing tool. Deposit metadata, deposited-file identity, and timestamp proofs therefore remain unverified. The current mutable source files were compared in the stated relevant scope; equivalence to the historical PDFs or deposit is not asserted.

## Final scope of the verdict

The canonical linear-family query theorem is fully answered, with its exact 0.99 requirement obtained by the proved affine/linear amplification. The original has no gap affecting that target. The reviewed source also removes the auxiliary constrained algorithm's off-event definition ambiguity. No numerical stability, finite-bit implementation guarantee, query lower bound, human authorship validation, or priority conclusion is supplied. No canonical files were edited and nothing was published by this reviewer.
