# SP-14 exterior boundary square and zeros: independent Lean review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `BaseExteriorBoundarySquare.lean` against the approved pre-proof contract. It proves the square identity of the already normalized exterior circle series at **every** boundary point and its zero consequence whenever `z²=-1`. It does not construct an annular extension or the final SP-14 counterexample.

The independently elaborated theorems are

```lean
baseExteriorSymbol_sq (z : Circle) :
  baseExteriorSymbol z ^ 2 = (z : ℂ) ^ 2 + 1

baseExteriorSymbol_zero_of_sq_eq_neg_one (z : Circle)
  (hz : (z : ℂ) ^ 2 = -1) : baseExteriorSymbol z = 0
```

The proof uses the **actual boundary series terms** `f_n=c_n z^(1−2n)`. Their norms equal `‖c_n‖`, so the previously certified coefficient-norm summability supplies the explicit hypothesis of the complex Cauchy-product theorem. In each antidiagonal `p+r=N`, integer exponents combine to `2−2N` using `z≠0`; the finite coefficient convolution is `1` at `N=0` and `N=1`, zero otherwise. The resulting `tsum` is exactly `z²+1`, with no formal-power-series evaluation at a boundary point and no division at either zero. When `z²=-1`, the square identity gives a square equal to zero, hence the symbol itself is zero in `ℂ`. The series definition with `c₀=1` continues to fix the exterior branch; the square equation is only a verified consequence.

Pinned `lake build NLA.Proofs.SP14.BaseExteriorBoundarySquare` and a separate imported LeanCert audit of both exact signatures, `#assert_trust kernel`, and transitive axioms exited successfully under Lean 4.33.1. Each theorem lists exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseExteriorBoundarySquare.lean`** | **`93b81c168bf831439928020397bb14985f9fe26de2060e50c2c55a535c9e6239`** |
| `BaseExteriorSeries.lean` | `8e19c9af8809fc44414b90696a089d32417934475adc95f58aafa6db5b83dd0d` |
| `BaseCoeffSummable.lean` | `1da659ff573ddee8d598d32150fec45f7ae5d5eb023c2a9277a0500547ad9892` |
| `BaseCoefficient.lean` | `63dcd98bb3a45e77b2b0fd2644d444f9cfe866fb9dae5535d1b7cd1f73081bf4` |
| `BASE_EXTERIOR_BOUNDARY_SQUARE_PRE_REVIEW.md` | `84daf3905d3625d2f561f3dae9c2e0883c3a2d7d8bbffc93cc38280e22d72576` |
| `BASE_EXTERIOR_BOUNDARY_SQUARE_INDEPENDENT_PRE_REVIEW.md` | `7d13e47bb2ddf390ed402a52ab3447748b1dd54f04603e14af1b182fea4a69e3` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Independent `/private/tmp/sp14-baseexteriorboundarysquare-independent-audit.lean` | `d50d19c26a4dca02e5596bed1f55d83a5dd4176bd52129588035ce7dbf64aba8` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or approved contract bytes reopen this review. The final packet-modified symbol, its two-sided nonextension, test separation, and empirical gap remain open.
