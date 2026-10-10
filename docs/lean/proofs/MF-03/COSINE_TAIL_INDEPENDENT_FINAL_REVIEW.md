# MF-03 cosine tail: independent Lean source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `CosineTail.lean` as a kernel-checked proof of the exact numerical tail lemma in the approved pre-proof contract. It does not prove the separate `f(3)` estimate, Padé existence, Schur coefficient bounds, a disk bound, or the full all-order MF-03 `Target`.

`cosineFactor ν` is exactly `1/[π²(ν−1/2)²]`; `cosineTail m` is the infinite sum at `ν=m+k+1` for `k≥0`, hence starts at `ν=m+1` and is the manuscript's `S_m`. The public theorem has the precise elaborated signature `∀ m:ℕ, 1≤m → cosineTail m < 1/(9m)`, with strict inequality and no hidden `m≥16` premise.

The source defines `telescopingTerm m k=1/(m+k)−1/(m+k+1)`, proves it nonnegative for `m≥1`, proves its first `N` terms sum to `1/m−1/(m+N)` by induction, and obtains `HasSum ... (1/m)` from the reciprocal limit. For `n=m+k≥1`, it establishes `n(n+1)≤(n+1/2)²` and therefore the pointwise comparison `cosineFactor(m+k+1)≤(1/π²)·telescopingTerm m k`. The comparison proves summability of the cosine tail and `S_m≤1/(π²m)`. The pinned `Real.pi_gt_three` then gives `π²>9`; multiplication by positive `m` makes the final bound strict. This is the exact telescoping alternative approved before implementation, and every endpoint is consistent with the manuscript.

The module does not claim the numerical specialization `m≥16 → 6S_m<1/24` or the `f(3)≤6179/2120` ledger; these remain easy but separate Lean statements. More substantially, the Euler product, existence of normalized Padé pairs, and Schur/tableau coefficient bound still need formal proofs before this tail can support the all-order target. The frozen order-1–15 theorem remains a separate finite result.

Pinned `lake build NLA.Proofs.MF03.CosineTail` and a separate imported audit of the elaborated definitions and theorem, `#assert_trust kernel`, and `#print axioms` passed under Lean 4.33.1. The theorem's transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/MF03/CosineTail.lean`** | **`41fc5b7da2f1033b17608a56507aeeba555099f933a1b5eea05477331e8ace8b`** |
| `ALL_ORDER_TAIL_PRE_REVIEW.md` | `d25c72b46df6115b75e07e92f44a6a10a9b78e333d37c0561b49eefe20eba130` |
| `ALL_ORDER_TAIL_INDEPENDENT_PRE_REVIEW.md` | `ee0aefa199d5b306f5503788c37ef76bc83c68c4b4025308ff4406cc989e7dcd` |
| Canonical `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| Source manuscript `MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| Frozen `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| Independent `/private/tmp/mf03-cosinetail-independent-audit.lean` | `c6e9314437f961d6c4dbbf7c9c14815552f5ca29fdcae6a44c7eddeda8fdfb3e` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or contract bytes reopen this review.
