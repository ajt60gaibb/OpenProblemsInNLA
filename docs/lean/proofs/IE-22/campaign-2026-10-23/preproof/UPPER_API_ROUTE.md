# Independent IE-22 upper-route API research

Researcher: OpenAI Codex AI agent `/root/proof_route`, 23 October 2026.
Status: mathematical route and pinned-library inventory only; no theorem implementation.
The selected exact signatures are root's `Challenge.lean`. Wait for both
independent frozen-hash pre-proof approvals before writing implementation.

Pinned library inspected read-only:
`mathlib` 0df444a360eaa60ab8c11dca51a86af692955474 under
`/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages/mathlib`.

## Recommended elementary substitute

The pinned Probability tree contains no Gaussian Poincare theorem, Efron-Stein
inequality or general product-variance tensorization theorem. Such a theorem
is unnecessary for this qualitative upper endpoint.

For centered jointly Gaussian real X,Y, let v=Var(X), q=Cov(X,Y). If v>0,
set Y'=Y-(q/v)X. The pair (X,Y') is genuinely jointly Gaussian and uncorrelated,
so X and Y' are independent. Y' need not have Y's marginal law. For real
Lipschitz f,g with constants Lf,Lg, all needed second moments exist and

    Var(f(X)) <= E[(f(X)-f(EX))^2] <= Lf^2 v.
    Cov(f(X),g(Y)) = E[(f(X)-Ef(X))*(g(Y)-g(Y'))].
    E[(g(Y)-g(Y'))^2] <= Lg^2*q^2/v.

Cauchy-Schwarz therefore gives abs(Cov(f(X),g(Y))) <= Lf*Lg*abs(q).
The v=0 case is separate: X=0 almost everywhere (or, for the actual linear
forms, its coefficient vector is zero), so its covariance vanishes.
This is an actual theorem to prove, not a premise to add to the endpoint.

For f_t(z)=max(t-z^2,0), t>=0, its real Lipschitz constant is at most
2sqrt(t). Thus Var[(1/m)sum_i f_t(b_i dot G)] is bounded by
4t/m^2 times sum_(i,j) abs(b_i dot b_j).

After deleting r largest covariance directions, B has row norms <=1,
trace(B^T B)<=m and eigenvalues bounded by m/(r+1). Finite-sum Cauchy-Schwarz
and trace-of-square give

    sum_ij abs((B B^T)_ij)
      <= m*sqrt(sum_ij ((B B^T)_ij)^2)
      = m*sqrt(sum_j lambda_j^2)
      <= m^2/sqrt(r+1).

Consequently Var(Psi_t)<=4t/sqrt(r+1). This is slower than the source's
Poincare rate and sufficient for the exact requested qualitative endpoint.
No claim of proving the stronger source rate should be made.

Choose L=4/(1-theta). Markov gives P(||BG||^2/m>4)<=1/4. On its complement
the finite trimming dual maximum is attained in [0,L], including floor(theta*m)=0.
A finite mesh plus Chebyshev controls every t in [0,L] as r tends to infinity.
For each requested error choose one fixed sufficiently large natural r;
then choose the ambient threshold n sufficiently larger than r. There is no
need to formalize the source's n^(2/3), n^(-1/6) schedule.

The norm-square concentration need not compute E(G^4)=3. Let the finite real
constant K=Var[(fun x=>x^2);gaussianReal 0 1]. Gaussian fourth integrability
makes the square variable MemLp2. Independent sums yield Var(||G||^2)=d*K,
while E(||G||^2)=d follows directly from the unit variance and zero mean.
Chebyshev gives a bound K/(d*delta^2), sufficient here. Exact K=2 is optional.

## Available exact pinned APIs

- Probability/Distributions/Gaussian/Multivariate:
  `stdGaussian`, `map_pi_eq_stdGaussian`, `stdGaussian_map`,
  `variance_dual_stdGaussian`, `covarianceBilin_stdGaussian`,
  `integral_id_stdGaussian`, `integral_strongDual_stdGaussian`.
  These describe actual Gaussian measures and genuine Euclidean isometries.
- Probability/Distributions/Gaussian/HasGaussianLaw/Def and /Basic:
  `HasGaussianLaw.map` and its actual continuous-linear maps; use maps of the
  actual standard Gaussian to establish a joint law of two linear forms.
- Probability/Distributions/Gaussian/HasGaussianLaw/Independence:
  `HasGaussianLaw.indepFun_of_covariance_eq_zero` (real scalar pair),
  `HasGaussianLaw.indepFun_of_covariance_inner`,
  `IndepFun.hasGaussianLaw`. No new Gaussian independence oracle is required.
- Probability/Moments/Covariance:
  `covariance_eq_sub`, `covariance_sub_right`,
  `covariance_const_mul_right`, `covariance_comm`,
  `IndepFun.covariance_eq_zero`, `covariance_fun_sum_fun_sum`.
- Probability/Moments/Variance:
  `variance_eq_integral`, `variance_eq_sub`, `variance_nonneg`,
  `variance_le_expectation_sq`, `variance_sub_const`, `variance_const_mul`,
  `covariance_self`, `variance_sum_pi`, `meas_ge_le_variance_div_sq`.
  There is no existing general Lipschitz-variance lemma in this file.
- MeasureTheory/Function/LpSpace/Basic:
  `LipschitzWith.comp_memLp` applies directly to Lipschitz functions vanishing
  at zero; subtract the value at zero and add the integrable constant for
  arbitrary real Lipschitz functions under these probability measures.
- MeasureTheory/Integral/Bochner/Basic:
  `integral_mul_norm_le_Lp_mul_Lq` and
  `integral_mul_le_Lp_mul_Lq_of_nonneg` are the existing integral Holder
  interfaces. Specializing to p=q=2 supplies Cauchy-Schwarz. Alternatively a
  private squared integral Cauchy lemma can be proved from positivity of the
  integral of a square, avoiding real half powers in repeated use.
- Probability/Distributions/Gaussian/Real:
  `variance_id_gaussianReal`, `variance_fun_id_gaussianReal`,
  `integrableExpSet_id_gaussianReal`, `memLp_id_gaussianReal`,
  `memLp_id_gaussianReal'`, `mgf_gaussianReal`, and
  `integral_gaussianReal_eq_integral_smul` (genuine density conversion).
  `IsGaussian.memLp_two_id` supplies the multivariate linear-form L2 bounds.
- Probability/Moments/MGFAnalytic:
  `iteratedDeriv_mgf_zero` computes arbitrary actual moments if an exact
  fourth moment is later desirable; it is not required by the qualitative route.
- Analysis/Matrix/Spectrum:
  `Matrix.IsHermitian.eigenvalues0` is named `eigenvalues₀` in source and is
  indexed by Fin(card n); `eigenvalues₀_antitone` supplies sorted order.
  `eigenvalues`, `eigenvectorBasis`, `mulVec_eigenvectorBasis`,
  `trace_eq_sum_eigenvalues`, `spectral_theorem` provide the spectral data.
  Be careful: the matrix-indexed `eigenvalues` are reindexed by a cardinal
  equivalence, so do not assume that their original matrix index order is sorted.
- Analysis/Matrix/PosDef:
  `Matrix.PosSemidef.eigenvalues_nonneg`,
  `Matrix.eigenvalues_conjTranspose_mul_self_nonneg` establish actual positivity.

- Analysis/InnerProductSpace/Spectrum and /Trace:
  `LinearMap.IsSymmetric.eigenvectorBasis`, `eigenvalues_antitone`,
  `apply_eigenvectorBasis`, `toMatrix_eigenvectorBasis`, and
  `trace_eq_sum_eigenvalues` permit directly using an ordered Fin n eigenbasis
  of the actual `Matrix.toEuclideanLin` covariance. This avoids the matrix
  index reindexing issue noted above.

## Remaining upper implementation components

1. Nonempty bounded actual energy infimum and elementary finite trimming dual;
   root and route author should agree module ownership before duplicating these.
2. Ordered covariance eigenbasis truncation, unit projected row bounds, and the
   finite Gram absolute-sum estimate. All norms must be Euclidean, not function
   supremum norms.
3. Scalar bounded hinge Lipschitz/covariance and actual Gaussian projection laws.
4. Gaussian hinge expectation bound by the literal `TrimmedMoment a`, using the
   actual quantile event, with density/interval-integral conversion.
5. Finite mesh, genuine measurable events, Markov/Chebyshev finite union, actual
   positive-measure realization and normalized orthogonal lift.
6. Fixed-r then large-n epsilon bookkeeping to `uniform_squared_upper`.

This report asserts no proof, no completed kernel check of a mathematical
endpoint, no full Target and no new CI receipt. It does not modify frozen
source, canonical IDs, originals, or the historical incomplete project.
