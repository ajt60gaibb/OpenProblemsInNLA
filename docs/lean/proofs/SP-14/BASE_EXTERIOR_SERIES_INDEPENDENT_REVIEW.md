# SP-14 normalized exterior boundary series: independent Lean review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `BaseExteriorSeries.lean` for its exact series definition, pointwise absolute summability, and continuity. It does not yet prove Fourier coefficients, the square identity or boundary zeros, an outer annular extension, the odd Toeplitz characteristic polynomial, or the final SP-14 counterexample.

The definition is precisely `baseExteriorSymbol z = ∑' n:ℕ, baseCoeff n · (z:ℂ)^(1−2n)`, with the exponent in `ℤ`. Its `n=0` term is `z` because `baseCoeff 0=1`, fixing the normalized exterior branch through the series rather than by an ambiguous square equation. For every circle point and integer exponent, `‖z^ℓ‖=1`; the proved term-norm equality is therefore `‖baseCoeff n · z^(1−2n)‖=‖baseCoeff n‖`. The previously reviewed unconditional summability of the coefficient norms yields pointwise absolute summability. `continuous_tsum` applies the same summable bound uniformly to continuous integer-power functions, establishing continuity at every circle point. The theorem does not assert that any particular point is a zero; its source comment's reference to future zero points is descriptive only.

Pinned `lake build NLA.Proofs.SP14.BaseExteriorSeries` and a separate imported LeanCert audit of the elaborated definition and both exported theorem signatures, `#assert_trust kernel`, and transitive axioms exited successfully under Lean 4.33.1. Each theorem lists exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseExteriorSeries.lean`** | **`8e19c9af8809fc44414b90696a089d32417934475adc95f58aafa6db5b83dd0d`** |
| Imported `lean-statements/NLA/Proofs/SP14/BaseCoeffSummable.lean` | `1da659ff573ddee8d598d32150fec45f7ae5d5eb023c2a9277a0500547ad9892` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_EXTERIOR_SERIES_FOURIER_PRE_REVIEW.md` | `aed55ffe098560355c0f7dbeecdd313d42bf53ecd93bc1633c7f8299d459b67d` |
| `BASE_EXTERIOR_SERIES_FOURIER_INDEPENDENT_PRE_REVIEW.md` | `b552251955b3030f59e7de5444504fd60bae4ec15bbdecf368da8273b533a800` |
| Independent `/private/tmp/sp14-baseexteriorseries-independent-audit.lean` | `5562a24405195d120c8f3963c54b0f7a276ee49fdbc2607c9e5efd08321c070e` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or contract bytes reopen this review. The next analytic step is a justified interchange with the actual frozen real-interval Fourier integral for every integer frequency.
