# IE-21 independent preproof statement review 2

Date: 2026-09-22. Reviewer: `reference_review`, Codex AI agent. **Verdict: APPROVE the exact statement boundary identified below for proof implementation after the coordinator records both independent approvals and freezes it. No changes requested.** This is statement/correspondence approval only: all 23 Challenge declarations still have intentional reference placeholders and none is proved by this report.

## Independence and scope

I did not author or edit IE-21 Definitions, Challenge, numerical targets, configuration, or proposed proofs. I independently read the complete canonical README, the complete retained IE-21/IE-22 manuscript, every definition and every Challenge statement, the numerical targets, Comparator configuration, package pins, README, author receipt, and typecheck driver. My separate `../source-review.md` records the source-level quantitative checks and their limitations. Earlier authorship of unrelated MF-03/TR-27 modules is not IE-21 proof authorship. This review is independent of the IE-21 boundary author; it does not rely on the coordinator's verdict.

I performed a separate Lean 4.33.1 typecheck using a fresh external output directory and pinned cached dependency oleans. Definitions exited 0 with no warnings. Challenge exited 0 with exactly 23 expected `sorry` warnings. The retained command/output log is `referee-2-statement-typecheck.log`. This was not a clean dependency rebuild, Linux Comparator run, or proof verification.

## Complete-target correspondence

- **Original statement and IDs:** the full canonical mathematical problem-statement section occurs verbatim in `NUMERICAL_TARGETS.md`. The ID, canonical path, retention convention, Gaussian integral, every-sequence quantifiers, and requirement of quantitative bounds are preserved. The source proof remains attributed to Matthew J. Colbrook. Formalization credit uses George Stepaniants and the requested Caltech department affiliation, without adding an email.
- **Euclidean matrices:** `Space n` is actual real Euclidean space. `matrixMap` is the continuous-linear-map version of `Matrix.toEuclideanLin`; `operatorNorm` is its genuine induced norm. The required coefficient, norm-attainment, norm-bound, and retained-squares identities cover the matrix interpretation. No entrywise matrix norm is substituted.
- **Minima and zeros:** `deletionSingular` ranges over precisely the row subsets of cardinality `Nat.floor(θm)` and all unit vectors. `deletion_minimum` requires attainment, a lower bound against every admissible pair, and nonnegativity. `deletion_zero_cases` includes empty retained sets and any retained map with a nonzero kernel vector. `finite_trimming_semantics` requires actual finite minimization and an attained threshold maximum, including `k=0` and `k=m`; `directional_minimum` supplies both attainment and the universal lower bound. Consequently no `sInf` default can stand in for a missing extremum.
- **Actual spherical law:** `surfaceMeasure` is Euclidean volume transported to the sphere by Mathlib's polar construction; `surfaceLaw` literally normalizes its mass. Probability, finite positive mass, and sphere support are required conclusions for every positive dimension. `matrixLaw` is a product of these laws pushed through row coordinates. Its independence and marginals are conclusions. Gaussian direction is a separate object whose equality in law, zero-nullity, radius independence and exact radial moments must be proved. None of these substantive conclusions appears inside a hypothesis.
- **Arbitrary random rows:** the only row-law hypotheses in `IndependentSphereRows` are matrix measurability, row independence, and the specified normalized spherical marginals. `independent_row_transport` must prove equality to `matrixLaw`. `original_random_row_limit` permits arbitrary and different probability spaces for each index. It adds no coupling across dimensions and no stronger aspect-ratio condition. Positive dimensions match the source's matrix/sphere convention; the finite restriction `n≥2` holds eventually under the original `n→∞` assumption. No condition on retained rank or `floor(θm)≥n` is introduced.
- **Canonical Gaussian constant:** `gaussianTrim` is the displayed density integral. `gaussian_constant` requires a positive cutoff with exact Gaussian mass θ, uniqueness, and equality to the truncated second moment. Endpoint inclusion is harmless for the continuous Gaussian law. The bound `[0,1]` suffices for the ratio estimate; the constant cannot become an arbitrary supplied scalar. `populationTrim` is the actual threshold-dual supremum, used only as an intermediate interface. For the actual nonnegative integrable inputs its objective set contains zero and is bounded above by the mean; its definition does not contain a solution assertion. Its required concentration/comparison declarations cannot substitute it for the explicit final Gaussian constant.

## Numerical and logical checks

The exact pointwise floor correction is `L/m`; `L=2/(1−θ)`. The `2Lε`, `2(1+t)δ`, radius error `sqrt(2/n)`, covariance denominator `512`, MGF coefficient `32`, and failure coefficients `2` and `5` agree with the manuscript. The moment product has factors `2j+1` and `n+2j`, including the empty-product case `r=0`. `sphere_net` requires actual unit net points and covers every unit vector with the dimension-dependent bound; a merely finite net cannot discharge it.

`GoodEvent` quantifies over **all** unit directions and retains the covariance operator event. `statistics_measurable` requires measurability of the relevant statistics and good event. `finite_size_bound` bounds the probability of failure of the simultaneous operator-positivity, normalized operator, normalized deletion, and ratio conclusions. This is valid even when its numerical upper bound exceeds one. Its domains `m≥1,n≥2`, `0<t,δ<1`, and `0<ε≤(1−θ)/2` are correct. In particular `1−t>0` is guaranteed, not silently assumed after division. The arbitrary-row finite theorem follows the same exact ratio bound.

`aspect_schedule` requires eventual admissibility and limits of both explicit error and failure expressions for the source's schedule `32 sqrt(log Q/Q)`. It assumes only `n→∞` and `Q=m/n→∞`. `spherical_ratio_limit` and `original_random_row_limit` assert vanishing probability of every positive absolute-error event. This is precisely convergence in probability on changing finite-dimensional spaces. The finite certificate alone would not satisfy the boundary.

No `axiom`, proof hole, user-supplied success predicate, conditional concentration theorem, numerical oracle, hidden Gaussian representation, or conclusion-bearing structure was found in Definitions. The only deliberate holes are the 23 Challenge reference proofs. All intermediate statements inspected are mathematically consistent with the source, including the more general harmless cases `m=0` in some pure semantic lemmas and arbitrary positive net radius.

## Configuration and operational limits

The Comparator theorem list matches all 23 Challenge declarations exactly, in order, without duplicates. Its permitted axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`; `definition_names` is empty. The shared custom Definitions are reviewed explicitly here rather than hidden behind definition holes. Package pins match Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.

README and numerical targets truthfully describe a statement-only draft with no Solution or successful Comparator run. No `formalization.yaml` exists in this draft yet, so no schema/metadata approval is claimed. Publishing a complete verification later still requires truthful metadata, implementations independent of Challenge, kernel trust checks for every selected declaration, exact Comparator correspondence, permitted-axiom closure, reproducible verification, and independent final proof review. These future requirements do not weaken this approval of the current mathematical boundary.

## Exact reviewed bytes

The author receipt's hashes were independently recomputed and all matched before this report. The canonical excerpt was checked verbatim and all 23 configured theorem names were mechanically matched to Challenge. Mathematical/configuration bytes are frozen by the following SHA256 identifiers for this review; changes require review of the affected scope.

```text
8f5b34b3db51676c93701b2919371c2d9a9dab95a2dd2e916935393d0804bbe1  NLA/IE21/Definitions.lean
f6eaea7248f2627a1d10e90808801e10c99a58060bd663797bdaa2aef43cb666  Challenge.lean
cbffbc10c1a046d3e33b7e2bbbdb6bd9f6e3da1088a9b2e6b40c72ccf24f03dc  NUMERICAL_TARGETS.md
48f805301dce0197794a59bddcd7f0c92026f0f833cd5b5597ed77fe736ecd9b  comparator.json
d7029127d42d9fe7945fa64b48e8dc0964691e53008895fbf2c97bb11b592977  lakefile.toml
48fd404fb76a69568e06f484f0662772458ec133b31a02224e58b26f7964601d  lake-manifest.json
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
d0f9cd5d0de4050fbb7ba827b3f21e51ba5c6217767b2ebda5a60c4b03d8901b  README.md
1aca518d7b6380c19dd03b58d7b0cbada690e143be391bdcede5c6bc01256b10  reviews/typecheck.py
9884c8fdd43cc3856f9b96510fa8e0c5769dbe47ea69b6ba2554bb1eb11c7972  reviews/statement-draft.json
171e4220e04233efcea4d46db73d6fca3071061df694e0645f340b4f4ff03ab1  reviews/statement-typecheck.log
d37864af3d57c8a62fa7dc5ddd589e757eaeeb2274942bf7585013b9435d69e7  reviews/referee-2-statement-typecheck.log
```

Supporting source receipts:

```text
1d5b73606664dd9af13078553f3311cabd947543b83a093f4060c5765cf42a6a  linear-systems-and-elimination/IE-21/README.md
31a1949c07f63408538f04e3803d90e8d3d0c3d1e47dc89a2ffa5a04ef4f3880  references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex
86bbf49cf95841a829324d73c3e0f32a924d8a779676e5211e0e58d6b0934b4b  docs/lean/campaign/2026-09-22/IE-21/source-review.md
```
