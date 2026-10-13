# MF-03 cosine product interface: independent partial source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `CosineProduct.lean` for its **three stated partial theorems and exact definitions only**. It does not prove convergence of the partial products to the wave series, their infinite-product identity, a Padé representation, or the full frozen MF-03 `Target`.

The source defines `waveSeries z = ∑' j, z^j/(2j)!` over `ℂ`, with exactly the frozen target's coefficient sequence, and `cosinePartialProduct N z = ∏_{k<N}(1+cosineFactor(k+1)·z)`. Thus the first factor is `ν=1`, namely `1+4z/π²`, and `N=0` is the empty product. The imported `cosineFactor ν` is exactly `1/[π²(ν−1/2)²]`, with a positive sign and no factor at `ν=0`.

The exported `cosineFactors_multipliable z` proves the pointwise complex product exists by summability of the shifted real p-series `∑(k+1/2)⁻²`, positive scaling by `1/π²`, and the norm majorant `cosineFactor(k+1)·‖z‖`. This is a genuine convergence fact; it does not identify the product's value. `waveSeries_zero` checks the exact normalization `1`. `waveSeries_three_eq_waveAtThree` casts the same factorial series at `z=3` to the previously certified real `waveAtThree`; it does not assert a new numerical bound or a general series-product equation.

The independently elaborated public signatures match these three claims. Pinned `lake build NLA.Proofs.MF03.CosineProduct` and a separate imported LeanCert audit of definitions, signatures, kernel trust, and transitive axioms exited successfully under Lean 4.33.1. Each theorem uses only `[propext, Classical.choice, Quot.sound]`. The source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/MF03/CosineProduct.lean`** | **`a80cd280636110b108e0a13702a55c57d15b739cfc1e73f73bd76eb330689c8a`** |
| `COSINE_PRODUCT_PRE_REVIEW.md` | `b78f8d9255dee8ffd2a6c4add6637ce95dbeaad6c61b3e87148bb101d3091b9a` |
| `COSINE_PRODUCT_INDEPENDENT_PRE_REVIEW.md` | `7cb877be8cc8c2db7f0fbde9529aa19d047020e3ea7eeaf86bc91aa9336a76a4` |
| Frozen `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `CosineTail.lean` | `41fc5b7da2f1033b17608a56507aeeba555099f933a1b5eea05477331e8ace8b` |
| `WaveAtThree.lean` | `824320b42ef6c052c12f6e68ebfb774a4ed969544a70f32a47cd0d8102682b6a` |
| Independent `/private/tmp/mf03-cosineproduct-independent-audit.lean` | `2f2d44bfd450c836d713acafa8372d0762c5c8c8a43da536536a44185139ac63` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or contract bytes reopen this review. The manuscript's all-complex Euler cosine product, coefficient extraction for the Schur matrix, all-order Padé existence, and disk bound remain open.
