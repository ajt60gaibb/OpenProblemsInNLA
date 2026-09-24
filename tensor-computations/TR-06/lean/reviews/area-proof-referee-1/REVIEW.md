# Independent contribution review: TR-06 area formula

Phase: post-proof contribution review. Reviewer: `/root/tr06_statement_referee_1`, AI agent. I did not author any of the six reviewed area modules. I previously reviewed the common statement boundary and authored separate linear-norm and rank-one-chart modules, neither of which is imported by this contribution. Review date: 2026-09-24. Reviewed boundary: `ab3e1a2e`.

**Verdict: APPROVE this area-formula contribution for integration.** This is not approval of the whole TR-06 formalization, a completed Comparator run, a Linux verification run, or status promotion. No substantive changes are requested to these bytes.

## Frozen sources

The review snapshots are under `source/`. They were read in full and freshly rebuilt into the previously empty `build/` directory. No author-produced contribution olean was used. All author manifest hashes match the snapshots and the current author files.

| Module | SHA256 |
|---|---|
| `NLA.TR06.NormDet` | `011d8e3aad6fc3fb3ba7e0c61441c7b0dc18e7a14380b6fa4e9a872e99b1be2a` |
| `NLA.TR06.Rectangular` | `ddea787637f1fc440d0f15bd3ad2c3432c2dde7697dafd54c439773a529ab717` |
| `NLA.TR06.LocalVolume` | `420610ff5afe6dbee87163a57fff594a21c96f41db7a6c552b1b6140a635d8fd` |
| `NLA.TR06.Density` | `422a5b4b0e3d887eaa3a0f7f2be4340b6ce7f4e8a68922ab47be6e350bd5c460` |
| `NLA.TR06.Radius` | `b223f5ddd8530190164d8e14df7ec3f7304b31158265d41130b3e7631093462c` |
| `NLA.TR06.Area` | `7c5ceb92698488553164d58ad0d2febb0f8b1b86c6c933a14c0f1d7fe2c74516` |

Approved common Definitions SHA256: `e5fe5314f4c17df41b5bec54f2c407b2d1eba8ba59be5d85525de13e262f8898`. Independently frozen Challenge SHA256: `5706c286e2d184965962c31c01805a4d119696459e5bc6e2f90226587e452fbe`. `boundary-check.json` records a byte-for-byte match of the complete `induced_volume_chart` header with that Challenge, followed by fresh elaboration of a reviewer-owned theorem of exactly that type using the implemented result. This is an additional local statement check, not Lean4 Comparator.

## Fidelity and mathematical correctness

`NLA.TR06.induced_volume_chart` proves the exact required equality on every measurable subset of the actual chart source. The domain is the Euclidean space of the declared expected dimension, the image is the chart's ambient tensor value, and the integrand is the normDet of its actual ambient derivative. The smoothness and derivative injectivity requirements are discharged from the unchanged DecompositionChart fields. Injectivity of the chart on its source is discharged using the genuine OpenPartialHomeomorph. No extra regularity, finite-volume, inverse-map, bounded-domain, or Jacobian-integrability hypothesis was introduced.

The general `NLA.TR06.Area.immersion_area` assumes an injective map, an explicitly provided within-derivative on each point of a measurable set, and injectivity of those derivatives. E and F are finite-dimensional real inner-product spaces with compatible Borel measurable structures; their dimensions need not agree. These are genuine hypotheses of the general theorem and are established by the chart application. In particular, it does not silently replace a rectangular derivative with an ambient determinant. Nonuniqueness of a within-derivative on exceptional domain points does not invalidate the proof: the density-point estimate controls the provided derivative almost everywhere on each measurable approximation piece.

The local metric argument reparameterizes only the image of an injective linear map. Its use of invFun is guarded by exact membership in that image and the proved left-inverse property. The Lipschitz and anti-Lipschitz factors are 1+delta*K and 1-delta*K; the lower argument explicitly establishes delta*K<1. Conversion of inverse factors in ENNReal proves the factor nonzero and finite rather than dividing a possibly infinite measured set. Radius.lean separates infinite-volume sets before using truncated subtraction; positive epsilon makes the required additive-error bound valid in that case.

The normalization is correct. `μHE[m]` is Mathlib's Euclidean-normalized Hausdorff measure, not raw `μH[m]`. I read the pinned definitions and the proofs of `LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume` and `InnerProductSpace.euclideanHausdorffMeasure_eq_volume`. The latter identifies this measure exactly with the domain's Euclidean volume. The common dimension-dependent factor is transported on both sides of the Lipschitz estimates. The imported file contains an unrelated `proof_wanted` about an explicit scalar-factor formula; this contribution does not use that declaration, as confirmed by the permitted axiom closure. No unproved numeric normalization formula is assumed.

The countable partition theorem is used with derivative samples from the original nonempty set; hence every sampled linear map is injective. Approximation pieces are measurable and pairwise disjoint. Image measurability follows from continuous-on and injective-on, with separability available from finite dimension. The lower measure summation explicitly proves images pairwise disjoint using map injectivity. The finite-volume intermediate result lets epsilon approach zero only after establishing finite domain measure. The final result exhausts arbitrary measurable sets by disjoint pieces of the sigma-finite volume spanning sets, proves each intersection has finite volume, and uses countable additivity and the disjoint-union lintegral identity. Thus unbounded sets and infinite total volume are covered without an omitted limiting assumption. No positive-dimension restriction is used; the zero-dimensional conventions are inherited from proved Mathlib results.

## Proof quality, reuse, API and attribution

I inspected the pinned Mathlib `MeasureTheory/Function/Jacobian.lean` partition and density machinery and `Analysis/InnerProductSpace/NormDet.lean` rectangular linear volume theorem. The extension uses those APIs and adds only the missing rectangular local estimates and assembly. The normDet continuity proof passes through its Gram determinant, preserving the induced metric. No numerical computation or interval certificate is needed. Names and namespace separate the reusable area lemmas from the frozen TR-06 target.

Density.lean and Area.lean explicitly retain Sébastien Gouëzel's 2022 copyright and explain their adaptation from his Mathlib Jacobian proof. The remaining modules credit George Stepaniants and the requested Department of Computing and Mathematical Sciences, California Institute of Technology affiliation, with no email. The documentation preserves Matthew J. Colbrook's original TR-06 proof attribution and accurately labels this as a partial contribution. I found no misleading complete-problem verification claim.

## Independent mechanical evidence

`recheck.py` compiled Definitions and all six contribution sources sequentially from the snapshots into fresh local output, using Lean 4.33.1 (commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6), pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, and pinned LeanCert 621a43d7cf21f87872392a01e874f2f1dbddc926. Dependency build caches were read-only. `fresh-rerun.json` records exact commands, LEAN_PATH, source/log hashes, timings, and exit codes. All seven exits were zero, with no warnings or errors. The source and logs show LeanCert kernel mode and successful `#assert_trust kernel` assertions. Every printed theorem axiom closure is exactly `[propext, Classical.choice, Quot.sound]`, including the final target and general immersion_area. The source scan found no sorry, admit, custom axiom, native_decide, unsafe/implemented_by declaration or Challenge import in the owned modules.

`boundary_check.py`, `source/ReviewBoundary.lean`, `boundary-check.json` and `logs/ReviewBoundary.log` preserve the reviewer-owned exact-target check and its kernel assertion. This review does not claim fresh dependency rebuilds, independent kernel reimplementation, Linux replay or Comparator; those remain integration gates. Final whole-problem fidelity/integrability and two independent final reviewers remain required before TR-06 can be promoted.
