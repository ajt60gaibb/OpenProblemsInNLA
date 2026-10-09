# IE-22: independent final Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for these bound bytes.

## Fidelity reasoning

1. RowDeletion was read in full. UnitVector and UnitRows use the full Euclidean sum of squares; RowValue is the ordinary real dot product. RetainedCount floors the real product theta*m.

2. SubsingularSquared ranges over every finite row subset of the exact retained cardinality and every unit vector. This is the square of the attained variational minimum on the positive-dimensional target domain. Empty retained sets and zero singular values are included. OperatorSquared takes the genuine complete unit-sphere squared-energy supremum.

3. UniformSphere normalizes actual Euclidean volume.toSphere by its ENNReal mass. The pinned HaarToSphere definition and finite/nonzero mass results were inspected; for positive n the normalized law is the uniform surface probability, including the two-point sphere in dimension one. No artificial measurable space or support-only uniformity condition occurs.

4. MatrixLaw is the full finite product of the same UniformSphere law, fixing independence. SampleMatrix extracts the actual Euclidean coordinates via WithLp.ofLp, so every row is a unit vector with that concrete law.

5. GaussianQuantile uses gaussianReal with mean zero and variance one, inspected in the pinned source. TrimmedMoment is the exact real integral with factor 1/sqrt(2*pi), integrand t^2*exp(-t^2/2), and endpoints -a,a. Since a>0, the oriented interval integral agrees with the source integral; endpoints have zero measure.

6. Extremum takes the real supremum over all unit-row real matrices of sqrt(n/m)*sqrt(SubsingularSquared). On positive dimensions this set is nonempty and bounded; no default empty/unbounded supremum value or random-ensemble restriction enters the canonical domain.

7. UniformUpper puts every epsilon>0 before existential natural N,R, then every positive n,m with N<=n and R*n<=m. This is exactly the original eventual dimension/aspect-ratio uniformity; thresholds cannot depend on a later matrix or dimension.

8. Target explicitly conjoins the upper property at sqrt(TrimmedMoment a) and its failure for every smaller real c. The negation applies to the complete same property; it preserves the original optimality quantifiers including negative candidate constants.

9. The erroneous old extra SupremumConverges condition is absent, as required by the reviewed specification. No stronger all-m rate theorem or matrix probabilistic assumption is silently added.

10. Live/frozen source bodies were mechanically compared, allowing only the standard comment and namespace rename. The shared RowDeletion and Infrastructure modules, all pins, notes and full original source/specification are bound through the actual local import closure.

11. The retained fresh author-local root macOS receipts report successful shared/live/frozen compilation and actual rfl identity checks. Logs report only propext, Classical.choice and Quot.sound. This reviewer inspected the evidence and definitions; it did not independently run Lean or Linux Comparator. No catalog proposition is proved by the statement declaration.

## Pinned external definitions inspected

- Mathlib/MeasureTheory/Constructions/HaarToSphere.lean: fc6efc9291ce6bcc2d8310b16f60087621470d2eb9cc10a0bfe47ebf413fabda; toSphere definition, cone formula, nonzero and finite total mass.
- Mathlib/MeasureTheory/Constructions/Pi.lean: 8751b21ac855f1a7b7c63258e8325f75b6fc236d360758b822ddf54597b118bf; Concrete finite product-measure construction.
- Mathlib/Probability/Distributions/Gaussian/Real.lean: f86827f9c60d435c5dfeffee1ac6d95f5a953c98703bdc1c653a368c23a2365b; gaussianPDFReal and gaussianReal, mean/variance convention.
- Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean: 93908eb0c771ba8edcb47537dfe1a40e98a1545be9d427c1eb9823d44decdcd5; intervalIntegral and integral_of_le, orientation and endpoint convention.
- Mathlib/Analysis/InnerProductSpace/PiL2.lean: 1f9827b2db67213c725a2dcc3fec52a87772966d1fbd3fc6857a019dbd7a6053; Genuine Euclidean space and coordinate representation.

## Bound inputs

- docs/lean/statements/IE-22/IMPLEMENTATION_NOTES.md: fe7668de77daaacb69b98e52ba2bb89c04f85b2cd492b18b4cdfab3b434d461c
- docs/lean/statements/IE-22/NUMERICAL_TARGETS.md: f42039df583dc45692c44053fbb69dcf713c04296be55a2b3b3972b2a7a92ece
- docs/lean/statements/IE-22/ORIGINAL.md: 273ce377e8de3f575be53104f156f0436ffb571a3a464bb5d5693c0aa510c344
- docs/lean/statements/verification/2026-09-28-row-deletion/CheckRowDeletion.lean: 56fc637750d8d92eb35e1e7161dc60bdca8db1ffc616e392d0a0484a072fd9ee
- docs/lean/statements/verification/2026-09-28-row-deletion/CheckRowDeletion.log: 9ae73aa589aa61aadffbd6d685a0cb2342ca8658acb11ad159e16f486dfb1250
- docs/lean/statements/verification/2026-09-28-row-deletion/NLA-Statements-IE21.lean.log: 2b09f250d6820b18e3803630d52b3499c00a16e82212a8ca54bcfb460346e84c
- docs/lean/statements/verification/2026-09-28-row-deletion/NLA-Statements-IE22.lean.log: 727b83fd3a2841355446f4d45b7d1b684d33df6c202faefe881f01b2b2146a08
- docs/lean/statements/verification/2026-09-28-row-deletion/NLA-Statements-RowDeletion.lean.log: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- docs/lean/statements/verification/2026-09-28-row-deletion/Reviewed-IE21.lean.log: 4075d3c93899be82144eabce679ae22994bf9d5fb69920d48b579b5329a8dfcd
- docs/lean/statements/verification/2026-09-28-row-deletion/Reviewed-IE22.lean.log: aa67719db751110f3d51d97ae23413602d7cea37944339eff9d7f6e2238e8391
- docs/lean/statements/verification/2026-09-28-row-deletion/receipt.json: e7a700745478b94731a81189a3ea44149f63b63e28eee04b874cdc804b552c3b
- lean-statements/NLA/Statements/IE22.lean: ba02136d23a3065c7764ac6b6d6c8a8712fc89862664cccc11dbf2c038f83d05
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/NLA/Statements/RowDeletion.lean: e8e7fd9a7e38961d319fc70c44c56d34444c2e5420b8d973d08b367d60ebb36b
- lean-statements/Reviewed/IE22.lean: f1ace8628bc239062f40f4d7a04892b96c70a133ba7cd3b10afdba38a92d9aaf
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71
- linear-systems-and-elimination/IE-22/README.md: 273ce377e8de3f575be53104f156f0436ffb571a3a464bb5d5693c0aa510c344

## Limits

Independent AI-agent final source-level fidelity review, independent of specification author /root/infra_audit and implementation author /root. Approval concerns the exact mathematical meanings and bound source bytes, not target truth or an independently executed kernel/CI run.
