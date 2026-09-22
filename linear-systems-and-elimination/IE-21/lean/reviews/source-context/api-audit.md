# IE-21 bounded library/API audit

Date: 2026-09-22. Auditor: Codex AI subagent `/root/infrastructure_audit`. This is a read-only mathematical/API scouting report, **not a preproof statement approval, proof implementation, kernel verification, or human referee report**. I authored none of the IE-21 definitions or statements inspected. Only this audit file was created. No VM was started.

The requested four foundations have a credible route through existing Mathlib results. The main new bridge is the Gaussian radial-density/polar-product correspondence. Exact spherical moments then reduce to one family of one-dimensional Gamma integrals. The exact net cardinality needs a variable-radius version of an existing disjoint-ball proof. None of these bridges should be replaced by assumptions in the final target.

## Inputs and source-authentication limit

I read `IE-21-NEXT.md`, `next-target-linear-assessment.md`, the canonical `linear-systems-and-elimination/IE-21/README.md`, and the retained complete `references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex`. I also inspected the draft `IE-21/lean/Challenge.lean` and relevant definitions. The draft already selects the **exact all-orders moment identity**, not merely the moment inequality.

Library inspection used `/private/tmp/mf21-mathlib-source-20260920`, the retained source cache associated with the campaign's Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`; that pin is also recorded in the IE-21 draft manifest. This extracted tree has no Git metadata. I did not independently authenticate every file against the remote pinned Git tree in this task. The hashes below identify exactly the local bytes inspected; they are not a claim of fresh remote source authentication. Before final verification, the unchanged campaign harness must check the actual dependency HEADs and source receipts in its authenticated clean snapshot. No API snippets in this report were independently compiled, and source-search failures do not establish absence from every external library.

## Actual normalized sphere measure

The draft's definitions are appropriate starting points: `surfaceMeasure n = volume.toSphere`, `surfaceLaw n = (surfaceMeasure n univ)⁻¹ • surfaceMeasure n`, and ambient `sphereLaw n = (surfaceLaw n).map Subtype.val`. In particular, `toSphere` itself is generally **not** a probability measure.

In `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`, namespace `MeasureTheory.Measure`:

- Lines 87–105: `toSphere_apply_univ`, `toSphere_real_apply_univ`, `toSphere_eq_zero_iff_finrank`, `toSphere_eq_zero_iff`, `toSphere_ne_zero`, and the finite-measure instance. In a nontrivial finite-dimensional real normed space with additive Haar measure, total surface mass is `finrank ℝ E * μ (ball 0 1)`, finite and nonzero.
- Line 142: `measurePreserving_homeomorphUnitSphereProd` sends `μ.comap Subtype.val` on the complement of zero to `μ.toSphere.prod (volumeIoiPow (finrank ℝ E - 1))`. The radial density exponent is **dimension minus one**.
- Lines 255 and 296, now in namespace `MeasureTheory`: `integrable_fun_norm_addHaar` and `integral_fun_norm_addHaar` reduce radial ambient integrability/integrals to integrals over `Ioi 0`, with weight `r^(dimension-1)` and factor `dimension * μ.real (ball 0 1)`.

`MeasureTheory.isProbabilityMeasureSMul` at `Measure/Typeclasses/Probability.lean:99` gives precisely `IsProbabilityMeasure ((μ univ)⁻¹ • μ)` from `[IsFiniteMeasure μ] [NeZero μ]`. `Measure.isProbabilityMeasure_map` at line 124 then handles the ambient subtype map. The support statement is the preimage of the unit sphere under `Subtype.val`, hence the whole subtype, with measurability supplied explicitly.

New local work: obtain the nontrivial-space instance from `1 ≤ n`, expose the finite/nonzero measure instances, convert positivity/non-top facts as necessary, and prove the mapped support assertion. Do not assert positivity in dimension zero: the surface measure there is zero. The draft correctly guards this theorem by `n ≥ 1`.

## Gaussian direction, radius, and independence

Existing exact APIs in namespace `ProbabilityTheory`:

| File and line | Available result |
|---|---|
| `Distributions/Gaussian/Multivariate.lean:66,72` | `stdGaussian`, `isProbabilityMeasure_stdGaussian` |
| Same file:82,94,114 | `variance_dual_stdGaussian`, `charFun_stdGaussian`, `integral_strongDual_stdGaussian` |
| Same file:128,137,146 | `stdGaussian_map` for a linear isometry equivalence; `map_pi_eq_stdGaussian`; `stdGaussian_eq_map_pi_orthonormalBasis` |
| `Distributions/Gaussian/Basic.lean:47,123` | `IsGaussian.map_eq_gaussianReal`; `IsGaussian.memLp_dual` |
| `Distributions/Gaussian/Real.lean:225,275,580` | `gaussianReal_of_var_ne_zero`; `integral_gaussianReal_eq_integral_smul`; `memLp_id_gaussianReal` |
| `Independence/Basic.lean:703,727` | `indepFun_iff_map_prod_eq_prod_map_map`; `indepFun_prod` |
| `Independence/Integration.lean:380,423` | `IndepFun.integral_fun_comp_mul_comp`; `IndepFun.integral_fun_mul_eq_mul_integral` |

The normalized Gaussian direction law and radius/direction independence were **not located as already packaged theorems**. Orthogonal invariance alone is not the required equality with the literal normalized `toSphere` measure; a uniqueness argument would still require proof. The most direct route I recommend is:

1. Prove that `stdGaussian (Space n)` has radial Lebesgue density `c_n * exp (-‖g‖²/2)`, with `c_n = (sqrt (2*pi))^(-n)` or an equivalent positive expression. Start with `map_pi_eq_stdGaussian`, the scalar Gaussian density, and `PiLp.volume_preserving_toLp` (`MeasureTheory/Measure/Haar/InnerProductSpace.lean:139`). A finite-product density identity can be proved by equality on measurable rectangles and finite-product integration. I did not find a ready-made finite-pi `withDensity` identity in the searched files, so this remains a local bridge, not an assumed API.
2. Transfer that density along `measurePreserving_homeomorphUnitSphereProd`, on the complement of zero. The weighted product is `surfaceMeasure n` times a radial measure on `Ioi 0` with density proportional to `r^(n-1) exp(-r²/2)`. `Measure.prod_withDensity_right` and `Measure.prod_withDensity` (`Measure/WithDensity.lean:715,726`) supply the product-density algebra. Map/restriction transport can also be checked by measurable-set or nonnegative-integral extensionality, so a specially named density-transport lemma is not essential.
3. Normalize the two factors. The total joint mass is one, and the sphere factor has positive finite mass, so the angular marginal is **exactly** the draft's `surfaceLaw n`. Establish zero Gaussian mass at `{0}` from absolute continuity with respect to nontrivial Euclidean volume. Then extend the complement-of-zero polar statement to the draft's total `gaussianDirection`, whose value at zero is zero.
4. Project the product identity to obtain the exact ambient direction pushforward and `IndepFun norm gaussianDirection`. Prove measurability and all almost-everywhere identifications; do not confuse the sphere subtype with ambient space or silently drop the exceptional origin.

An alternative density proof is available through characteristic functions: `integrable_cexp_neg_mul_sq_norm_add`, `integral_cexp_neg_mul_sq_norm_add`, and `integral_rexp_neg_mul_sq_norm` in `Analysis/SpecialFunctions/Gaussian/FourierTransform.lean:267,315,329`, plus `charFun_stdGaussian` and finite-measure characteristic-function uniqueness. This avoids a finite-product density lemma but introduces complex-power normalization algebra. It is a fallback, not a second required development.

For arbitrary unit `x`, the real linear functional `g ↦ inner x g` has standard scalar Gaussian law using `IsGaussian.map_eq_gaussianReal`, mean zero, `variance_dual_stdGaussian`, and the norm of the inner-product functional. This avoids building a separate sphere rotation-invariance API just to change the coordinate direction.

The product-row and arbitrary-row law transports have direct support: `iIndepFun_pi`, `iIndepFun.map_fun_eq_pi_map`, and `iIndepFun_iff_map_fun_eq_pi_map` in `Probability/Independence/Basic.lean:891,840,860`. Map the resulting finite-product law through the explicitly inverse row/matrix maps. Measurability is required even when the product has no rows.

## Exact all-orders spherical moments

A Gamma-integral route handles the selected exact formula and the radius moments together. For an integer `k ≥ 1`, use the positive finite integral

`J(k) = integral_(0,infinity) r^(k-1) exp(-r²/2) dr`.

Existing integral and integrability results:

- Root namespace `integral_rpow_mul_exp_neg_mul_rpow`, `Mathlib/MeasureTheory/Integral/Gamma.lean:43`, states for `p > 0`, `q > -1`, `b > 0` that the integral is `b^(-(q+1)/p) * (1/p) * Real.Gamma ((q+1)/p)`. Substitute `p=2`, `q=k-1`, `b=1/2`; convert real powers to natural powers on `Ioi 0`.
- `integrableOn_rpow_mul_exp_neg_mul_sq` and `integrable_rpow_mul_exp_neg_mul_sq`, `Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:92,97`, supply the corresponding integrability hypotheses.
- `Real.Gamma_add_one` and `Real.Gamma_pos_of_pos`, `Analysis/SpecialFunctions/Gamma/Basic.lean:410,443`, give `J(k+2)=k J(k)` and the nonzero denominators.

Prove the recurrence once, then derive `E[R^(2r)] = J(n+2r)/J(n) = product_(j<r) (n+2j)` for `R=‖g‖` under the Gaussian law. Likewise, the even scalar Gaussian moment is `J(1+2r)/J(1) = product_(j<r) (2j+1)` by splitting the even density integral into its two half-lines. This needs no new chi-square distribution, Beta distribution, special double-factorial API, or symbolic differentiation of arbitrary-order MGFs.

On the Gaussian probability space let `U = gaussianDirection g`. Away from zero, `inner x g = R * inner x U`. Radius/direction independence therefore factors the even moment. Cancel the strictly positive radius moment to obtain exactly

`E[(n * (inner x U)^2)^r] = n^r * product_(j<r)(2j+1) / product_(j<r)(n+2j)`.

Integrability of spherical powers follows directly from the compact sphere support and `|inner x U| ≤ 1`; Gaussian and radial integrability is justified separately. Cover `r=0` explicitly: both empty products and the zeroth moment are one. For the bound, each denominator factor is at least `n`, and each odd numerator factor is at most `2*(j+1)`, yielding `2^r * r!`. No division is justified at `n=0`; the reviewed draft uses `n≥2`.

The same radial recurrence gives `E[R²]=n` and `E[R⁴]=n(n+2)`, hence `E[(R²-n)²]=2n`, exactly the last two conjuncts of `gaussian_surface_correspondence`. Cauchy–Schwarz then gives `E|1-R²/n| ≤ sqrt(2/n)`. Independence and `E[n*(inner x U)^2]=1` give the source's coupling estimate for squared projections. This must feed the actual population-trimming stability proof, not be presented as that proof by itself.

A Jensen bound would suffice for some concentration inequalities, but it does **not** prove the selected exact all-orders moment equality. It is therefore not a substitute under the present draft. No boundary change is requested here.

## Exact finite nets and cardinality

The required constant is `(1+2/δ)^n` for every `δ>0`, with centers on the actual Euclidean sphere and closed distance `≤δ`. At `δ=1/4` this is exactly `9^n`.

Available APIs:

- `Metric.IsSeparated`, `Topology/MetricSpace/MetricSeparated.lean:45`, uses **strict** separation `δ < edist x y` for distinct points. `Metric.IsCover` uses closed distance; these conventions match maximal-separated-set arguments without losing a factor of two.
- `Metric.exists_finite_isCover_of_isCompact`, `Topology/MetricSpace/Cover.lean:123`, supplies a finite internal cover at every positive radius.
- `Metric.packingNumber_two_mul_le_externalCoveringNumber`, `Topology/MetricSpace/CoveringNumbers.lean:330`, bounds the packing number by a half-radius finite cover. Thus a compact sphere has finite `δ`-packing number; the required conversion to `ℝ≥0`/`ℝ≥0∞` must be explicit.
- `Metric.exists_set_encard_eq_packingNumber`, `maximalSeparatedSet`, and `isCover_maximalSeparatedSet`, same file lines 270,291,309, give a finite maximal separated set that is a cover. Use the witness's finiteness or the finite cardinal identity when converting to a `Finset`.
- `Measure.addHaar_ball_of_pos`, `MeasureTheory/Measure/Lebesgue/EqHaar.lean:445`, gives `μ(ball x r)=ofReal(r^dim)*μ(ball 0 1)` for `r>0`. `measure_ball_pos`, `measure_ball_lt_top`, `measure_biUnion_finset`, `Metric.ball_disjoint_ball`, and `Metric.ball_subset_ball'` complete the volume calculation.

Most useful existing proof template: `Besicovitch.card_le_of_separated`, `MeasureTheory/Covering/BesicovitchVectorSpace.lean:109`. It proves `card ≤ 5^dim` for a 1-separated set in the radius-2 ball, by disjoint radius-1/2 balls inside radius-5/2, using precisely the APIs above. This is not directly the required theorem for arbitrary `δ`, but its proof generalizes with inner radius `δ/2`, enclosing radius `1+δ/2`, and centers of norm at most one. Cancel the positive finite unit-ball mass and divide by `(δ/2)^n` to obtain `(1+2/δ)^n` exactly. No explicit Gamma formula for Euclidean ball volume is needed.

The lower sphere-ball bound `toSphereBallBound_mul_measure_unitBall_le_toSphere_ball` in `HaarToSphere.lean:217` is weaker and involves `min(δ,2)/4`; using it as the net cardinality argument would change the finite-size constants. The ambient disjoint-ball proof avoids that loss. The statement includes `δ≥2`; the same volume proof works, or a singleton covers the sphere in this range. Do not add an unreviewed `δ<1` hypothesis to the selected `sphere_net` theorem.

## Suggested implementation order and acceptance limits

After both preproof approvals freeze the boundary: (1) normalized surface law and product-row semantics; (2) Gaussian radial density/polar product and its exact map/independence bridges; (3) the single `J(k)` recurrence, exact moments and radius coupling; (4) finite-net volume generalization, independently parallelizable; (5) concentration and trimming assembly with the unchanged constants and every diverging aspect-ratio sequence. The Gaussian bridge should be proved before moment/coupling modules consume it; it must not be added as an axiom or a hypothesis on rows.

This audit establishes API availability and a proposed route only. It does not discharge measurability, integrability, density transport, selected theorem signatures, the MGF sum/interchange, trimming optimization, covariance quadratic-form nets, or the final probability limit. Final completion still needs all selected proofs, independent mathematical/source review, genuine LeanCert kernel assertions, allowed-axiom audits, real Comparator controls, and reproducible verification under the shared harness. Preserve Colbrook's original proof attribution and the permanent canonical IE-21 ID/path.

## Local byte receipt

The following hashes were computed after this read-only audit. Paths beginning `Mathlib/` are relative to the retained source cache identified above; other paths are relative to the campaign worktree.

| File | SHA-256 |
|---|---|
| `docs/lean/campaign/2026-09-22/IE-21-NEXT.md` | `8b79a8f73f2b91ad3270a516b34d00786b3c2aedf6af6aa48fb340cefcd7cc5b` |
| `docs/lean/campaign/2026-09-22/next-target-linear-assessment.md` | `b607c37f99fe1cb718e1ad874ad2ef214d95f9aa8b5c2ad25033ca3a7965ff43` |
| `linear-systems-and-elimination/IE-21/README.md` | `1d5b73606664dd9af13078553f3311cabd947543b83a093f4060c5765cf42a6a` |
| `references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex` | `31a1949c07f63408538f04e3803d90e8d3d0c3d1e47dc89a2ffa5a04ef4f3880` |
| `docs/lean/campaign/2026-09-22/IE-21/lean/Challenge.lean` | `f6eaea7248f2627a1d10e90808801e10c99a58060bd663797bdaa2aef43cb666` |
| `docs/lean/campaign/2026-09-22/IE-21/lean/NLA/IE21/Definitions.lean` | `8f5b34b3db51676c93701b2919371c2d9a9dab95a2dd2e916935393d0804bbe1` |
| `docs/lean/campaign/2026-09-22/IE-21/lean/lake-manifest.json` | `48fd404fb76a69568e06f484f0662772458ec133b31a02224e58b26f7964601d` |
| `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` | `fc6efc9291ce6bcc2d8310b16f60087621470d2eb9cc10a0bfe47ebf413fabda` |
| `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean` | `ffdd255936488de3042812bbfd46aabe4beef01608cd356c50c9af25aea491cd` |
| `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` | `1fec35cf781da1009c37db80a96b05d70f2296ca7768e19bfc0b6314c9b43d49` |
| `Mathlib/Probability/Distributions/Gaussian/Basic.lean` | `d787d5341155cbd9ab7dc19de55c8cf490ab109f70ffd69a5560cbc7e110e556` |
| `Mathlib/Probability/Distributions/Gaussian/Real.lean` | `f86827f9c60d435c5dfeffee1ac6d95f5a953c98703bdc1c653a368c23a2365b` |
| `Mathlib/Probability/Independence/Basic.lean` | `85c6c98a306c1b10952181fcb9cc777c0ed06e91246428690a88d7821d24f9d2` |
| `Mathlib/Probability/Independence/Integration.lean` | `2db634dc88af5572dec0b49e79de4fd509c49f891b311cc76b318627a5d4786a` |
| `Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean` | `176ec47d5c89daf4d70e31fa237677305755d504dc0eedc2e0d803e592ea2d60` |
| `Mathlib/MeasureTheory/Measure/WithDensity.lean` | `b62c4ad72728e11a87bb3cefc6b968a081a70901030e8ac8e60d43b5ec2a8649` |
| `Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean` | `6bdd5e351d714198761da26ce7eac19a140a54218e9902dcf4fd41616d311523` |
| `Mathlib/MeasureTheory/Integral/Gamma.lean` | `56e1a1d4092f9864a3968364825967da12e57840ee3708cad651df987a8842f4` |
| `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` | `96a282f317e96505e89e51553f8129e52f381953dd142ee269f2525cb00f6197` |
| `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean` | `720a9a72d742fbe1c9a89601dc3a00d82c0261c7368c98cccb58307dbffe3bbf` |
| `Mathlib/Topology/MetricSpace/MetricSeparated.lean` | `6186c04ce51f640784389a21b25ab2890bccf67495baf5348b679d9d74dcad78` |
| `Mathlib/Topology/MetricSpace/Cover.lean` | `13d40953a0d05e017e6904e61a9d482e894f7933ae07003fec37c35f075299e7` |
| `Mathlib/Topology/MetricSpace/CoveringNumbers.lean` | `26f9b7db1b5c2ec25134f4c8296c87fb455e9af4ba789d53aa2501b6a2014d37` |
| `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean` | `269a2815cff12469aa8361d9062bfb11f8f7c45787799752b6e5bc3a7705e5a3` |
| `Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean` | `b59ddbc9cefe63c64fedf790c1444bfb1b7dcac741092fea3bd2670080898fdd` |
