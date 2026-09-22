# IE-21 independent covariance and ratio helper review

Reviewer: Codex AI agent `/root/canonical_inventory`. Date: 2026-09-22.
Verdict: **APPROVE the four exact module versions below**, with no mathematical or implementation findings. This is a bounded module review, not final independent whole-problem approval.

| Module | SHA-256 | Verdict |
|---|---|---|
| `QuadraticNet.lean` | `a28d33d754c4d196945572201b9629a49a05d77aca2dbd7787e882d4c3719bfa` | APPROVE |
| `Chernoff.lean` | `b47b6292ed4cadbcf18ce60f50afe7572c70db2c2de1c5004f2b04dc92d0227c` | APPROVE |
| `CovarianceConcentration.lean` | `a74ae23f5628f75f9ad043d0ca652f9ce3f8342b1f1be5753eca59998e736889` | APPROVE |
| `RatioAlgebra.lean` | `5ba090760500f35fcc5d6619d9c5ad06b0b737d36e60851c4eb9154a1f5d4192` | APPROVE |

## Independence and scope

I did not author or edit these four proof modules. I previously authored the IE-21 statement draft and MatrixSemantics, FiniteTrimming, UniformTrimmingGeometry, and UniformTrimmingBound. The reviewed proofs import some of that work; those semantic modules already have a separate root review. I therefore do not qualify as an independent final whole-problem referee. No canonical page, frozen target, status, or proof source changed in this review.

These versions contain 14 helper theorems and one definition. In particular, CovarianceConcentration contains only `directional_quadratic_tail_of_mgf` and `covariance_concentration_of_mgf`, both with explicit exponential-integrability and local MGF-bound hypotheses. No selected frozen target is newly claimed complete here. The separately added Covariance module and its SphericalMGF dependency are outside this approval. A future edit to any reviewed file requires review of the changed bytes.

## Mathematical review

**QuadraticNet — APPROVE.** The real quadratic-form estimate expands the difference into two inner products and uses the actual continuous-linear-map norm. The symmetric norm characterization is supplied by Mathlib's Rayleigh-quotient theorem and explicitly treats the zero vector before normalization. A unit-sphere δ-net yields the exact denominator `1−2δ` under its stated positive-denominator hypothesis; the δ=1/4 contrapositive gives threshold t/2. `covarianceOperator` is definitionally the frozen n/m-scaled adjoint product minus identity. Its quadratic forms match the actual matrix row energy, with no surrogate matrix, omitted symmetry requirement, or positivity/rank hypothesis. Zero-dimensional and zero-row algebraic identities retain the frozen totalized operations; the probability applications impose positive dimensions separately.

**Chernoff — APPROVE.** The sum MGF factors through actual independence. I checked the pinned Mathlib declarations `iIndepFun.mgf_sum`, `iIndepFun.integrable_exp_mul_sum`, and both exponential Markov bounds in Mathlib/Probability/Moments/Basic.lean. The tail theorem separately requires integrability at every local parameter, so a nonintegrable Bochner integral cannot masquerade as a finite MGF. Choosing ±s/64 is inside |a|≤1/8 for 0<s≤1; exact exponent arithmetic gives −m s²/128 on each side. Strict absolute-value failure is included in the two weak one-sided events, and m≥1 justifies division. The helper's MGF premise is explicit, not an added axiom or a completed spherical estimate.

**CovarianceConcentration — APPROVE.** The first helper obtains the actual product matrix law and independent surface-row marginals from the frozen measure model, composes row functions measurably, and transports both integrability and integrals through their pushforward equalities. The centered sum is exactly the covariance quadratic form. The second helper uses an internal 1/4-net of at most 9^n points and a finite union bound. Applying the first helper at t/2 yields exactly `2·9^n·exp(−m t²/512)`. It handles all m≥1, n≥2 and 0<t≤1 without a rank condition. Its only unfinished analytic input is visibly stated in its MGF premise; the two helpers do not themselves assert the unconditional selected target.

**RatioAlgebra — APPROVE.** The error hypotheses force e,t≥0 and v≥1−t>0. The numerator bound uses exactly 0≤h≤1 and yields |u/v−h|≤(e+t)/(1−t), with no unstated positivity assumption on u. The normalization identity cancels the nonzero scalar n/m under positive dimensions and remains valid when the operator norm is zero, using the same totalized real division as the frozen definitions.

## Independent reproduction

Ran `python3 reviews/covariance-referee-canonical-evidence/typecheck.py`. A new external output directory `/private/tmp/nla-ie21-covariance-independent-g4tg8jqp` was created. Definitions, the five necessary local dependency modules, all four reviewed modules, 14 independently applied literal theorem signatures, and all 15 public transitive axiom checks were rebuilt in 12 successful invocations. No author-created NLA olean was used; only the pinned package cache and these freshly rebuilt local outputs were on the effective import route. The build produced no error or warning. All 15 closures contain exactly the permitted standard three axioms: propext, Classical.choice, Quot.sound. Source scan found no sorry/admit/axiom/native_decide/unsafe or Challenge import in these four modules.

Lean is the pinned 4.33.1 Darwin aarch64 runtime. The input Mathlib and LeanCert pins remain those in the frozen package manifest. All four mathematical-boundary hashes still match statement-freeze.json. The source hashes were checked before and after the build. This is local kernel typechecking and axiom auditing, not the final Linux verifier, actual Comparator run, LeanCert full-target gate, or publication approval.

Raw log SHA-256: `b8cf0457351366f49eb31f58c2599033af6e4aa9db7266aab575f1cb23758c0e`.
Build receipt SHA-256: `60180195dbb8f18109eebe9798786dc0467a20d02d7f5783e99ceb8fecb83aae`.
Signature harness SHA-256: `fb99d5bb477eef4a5e025121336053c7500dc6f4cf11a6c2d6e51f60d902314e`.
Axiom harness SHA-256: `724ac9ad282ef3da3ce8ccc56a2155551f87bae5e3e0d32c94ea65ba7189d6ae`.
