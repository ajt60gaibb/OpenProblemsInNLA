# SP-14 exterior series termwise Fourier integration: independent Lean review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `BaseExteriorFourier.lean` for its exact all-integer Fourier-coefficient series theorem. It proves justified termwise integration for the normalized exterior boundary symbol under the **frozen real-interval Fourier integral**. It does not yet collapse the series to `BaseFourierPattern`, prove the base Toeplitz characteristic polynomial unconditionally, or supply the final SP-14 counterexample.

The independently elaborated public theorem is

```lean
NLA.Proofs.SP14.baseExteriorSymbol_fourier_tsum (k : ℤ) :
  NLA.Statements.SP14.FourierCoefficient baseExteriorSymbol k =
    ∑' n : ℕ, baseCoeff n *
      (if 1 - 2 * (n : ℤ) = k then 1 else 0)
```

The source uses the exact frozen `FourierCoefficient`: the interval is `0..2π`, the normalization is `1/(2π)`, and its phase is `exp(−ki t)`. For each integer `k` and term `n`, both the circle power and phase have norm one; the continuous integrand has norm `‖baseCoeff n‖` at every real `t`. The previously certified summability of those norms bounds the restrictions to the compact interval uniformly. `intervalIntegral.hasSum_intervalIntegral_of_summable_norm` justifies exchanging the series and interval integral; pointwise summability identifies the integrand as `baseExteriorSymbol (Circle.exp t)` times the frozen phase. The reviewed integer-mode orthogonality theorem then evaluates each normalized integral, including negative modes, to the displayed Kronecker condition. This is an actual analytic interchange, not a formal manipulation of an unproved `tsum`.

Pinned `lake build NLA.Proofs.SP14.BaseExteriorFourier` and a separate imported LeanCert audit of the exact signature, `#assert_trust kernel`, and transitive axioms exited successfully under Lean 4.33.1. The theorem lists exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseExteriorFourier.lean`** | **`837c00dc8cd034ddb8d7bc9672ada2d3f5f5a454a6e864ddfa42cf140b0332fd`** |
| `BaseExteriorSeries.lean` | `8e19c9af8809fc44414b90696a089d32417934475adc95f58aafa6db5b83dd0d` |
| `BaseFourierMode.lean` | `6744fba387ed60bbf05377478f20612f59a47fc5503f553e400dbce1d88cbbfe` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_EXTERIOR_SERIES_FOURIER_PRE_REVIEW.md` | `aed55ffe098560355c0f7dbeecdd313d42bf53ecd93bc1633c7f8299d459b67d` |
| Independent `/private/tmp/sp14-baseexteriorfourier-independent-audit.lean` | `43ee8903e82337bf797af976788d0df7d5bb86fe2d8b03822e82a5e72a98a4b6` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or approved contract bytes reopen this review. The remaining base-pattern step is elementary but still requires a Lean proof that the integer frequencies `1−2n` select exactly one term when appropriate and none otherwise.
