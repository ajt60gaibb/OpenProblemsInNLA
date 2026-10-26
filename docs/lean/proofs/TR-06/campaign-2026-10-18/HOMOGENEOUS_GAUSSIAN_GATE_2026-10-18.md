# TR-06 homogeneous Gaussian annulus gate: implemented API and scope

18 October 2026. Author: campaign agent `fr05_statement`. These five new support modules are frozen after a clean complete source replay. Independent source/kernel review is requested separately; this author report is not counted as independent review.

The modules prove the radial finiteness step using the **actual Euclidean Hausdorff measure** in the ambient normed real vector space. They replace the submitted source's polar-coordinate step by a dyadic-annulus argument. The original Colbrook problem solution remains the mathematical source of the angular Gaussian integrability strategy; the annulus proof is an explicit adaptation, not an assumed external theorem.

| New source in `lean-statements/NLA/Proofs/TR06` | SHA-256 |
| --- | --- |
| `HomogeneousGaussianScaling.lean` | `89a8ccf123dcb0050b080356499ad3df03d06ab4bbb01b64a1ab9b61cb7a65c5` |
| `HomogeneousGaussianSeries.lean` | `d825e4a2603c53275d92a48d86e04b3c1eb88e0c7251b682e1841056115eda25` |
| `HomogeneousGaussianAnnuli.lean` | `74b93c189f78f16bb36c9bc31976fd1bb11b82ea2c6a3b6cd694e1c28e51758d` |
| `HomogeneousGaussian.lean` | `76e16a0157420f5d60d896076e7875719f9144e4f04cb05a07823306211d15c9` |
| `HomogeneousGaussianMean.lean` | `f762fb4d19618622d7ee470a69af92366e9b1bbcc502f114231c3a4c208e658e` |

## Exact contracts

Namespace: `NLA.Proofs.TR06.HomogeneousGaussian`.

`annulus C` is exactly `C ∩ {x | 1 ≤ ‖x‖ ∧ ‖x‖ < 2}`. `PositiveCone C` is exactly `∀t>0, ∀x, t•x∈C ↔ x∈C`. `gaussian x` is exactly `ENNReal.ofReal (Real.exp (-‖x‖^2/2))`.

`gaussian_lintegral_lt_top q p hq` works in dimension `q+p`, with `q>0`. Given an actual measurable positive cone C excluding 0, a function f with literal degree -p homogeneity `f(t•x) = ofReal(t^p)⁻¹ * f(x)` on C, and finite literal annular integral of f against μHE[q+p], it proves the full Gaussian-weighted integral of f over C is finite. The dimension and weight are actual mathematical quantities; there is no manifold, polar-volume, semialgebraic-volume, finite-fiber or full-target theorem supplied as a hypothesis.

`gaussian_normalizer_lt_top` specializes p=0 and requires k>0 plus finite actual annular μHE[k]-volume. `gaussian_normalizer_pos` proves positivity from positive actual annular volume. `gaussian_numerator_lt_top` specializes p=1 and requires k>1 plus a finite actual annular integral of the degree -1 function. `finite_gaussian_mean_of_annulus` combines them: its Z is literally the Gaussian integral on C, and it proves `0<Z`, `Z<top`, and the literal Gaussian numerator divided by Z is less than top.

No extra f-measurability premise is needed for these finite nonnegative lintegral estimates. Measurability of the actual angular function and the probability-law statement remain separate obligations; the theorem does not claim either merely from finite outer lintegrals.

## Proof and reuse

`measurePreserving_scale` is proved from Mathlib's actual Euclidean Hausdorff homothety-preimage identity. It gives positive multiplication by t as a measure-preserving map from `ofReal(t^k) • μHE[k]` to μHE[k]. Its measurable-equivalence change of variables gives `lintegral_scaled_set`.

`cone_eq_iUnion_annulus` proves a genuine cover by all integer dyadic dilates using the real Archimedean zpow interval theorem. The scale of the f-integral is exactly t^q, derived by multiplying the actual Hausdorff scale t^(q+p) and actual f-scale t^(-p). The proof does not assume the scale of a hypothetical radial measure.

At negative integer scales the Gaussian is at most one and the positive exponent q gives a geometric summable majorant. At nonnegative scales the actual Gaussian is bounded by its value at the inner annular radius. The explicit ratio of the resulting coefficients tends to zero, so Mathlib's ratio test proves convergence. The countable-cover lintegral inequality and the proved finite ENNReal sum give the global integral bound. Positivity uses the everywhere positive actual Gaussian and monotonicity from annular volume to cone volume.

## Remaining actual-model obligations

This completes G4 as a reusable support gate. It does **not** prove TR-06's full Target or any of the five outstanding source-model exports. The full proof must still construct the actual full-measure tensor good locus, prove source-dimensional exceptional nullity, bound the actual annular normalized graph and its coordinate fibers, and apply the actual graph/area estimate to obtain the annular volume and angular-integral premises. A genuine nonempty regular chart and scaling must supply positive annular volume. The elementary model/tangent/normalization and induced-volume bridges must then identify the intrinsic frozen AngularCondition law with the candidate angular slope law.

The retained `angularSlope_pos_smul` already has the correct degree -1 formula at every point; the retained intrinsic rank/identifiability scaling provides the actual candidate cone. Once the three annular bounds and locus measurability/null restoration are established, these new theorems discharge the radial Gaussian step without an additional unit-link atlas or polar formula. Original d≥3, mode sizes≥2, r≥3, generic complex identifiability and all ten retained correspondence declarations remain unchanged.

## Mechanical and preservation evidence

`homogeneous-gaussian-development/result.json` records all five final source hashes and five successful builds. Every theorem printed in the logs passes LeanCert kernel assertions and has only `[propext, Classical.choice, Quot.sound]`. No axioms, admissions, sorry, native decision or external numerical certificate were added. This is local macOS evidence, not a Linux Comparator claim.

`preservation-checks.json` verifies all 58 copied retained modules and the live/frozen shared TR06 statement (60 byte comparisons) against the immutable preproof snapshot. Every comparison passes. No canonical README, original artifact, permanent ID, prior proof or frozen source was modified by this gate.
