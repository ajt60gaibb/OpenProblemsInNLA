# MF-03 cosine tail: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `ALL_ORDER_TAIL_PRE_REVIEW.md` for implementation of its exact numerical tail lemma. This is a preliminary large-order estimate, not an all-order Padé existence theorem, denominator coefficient theorem, disk bound, or proof of `NLA.Statements.MF03.Target`.

The proposed `cosineFactor ν = 1/[π²(ν−1/2)²]` and `cosineTail m = Σ'_{k≥0} cosineFactor(m+k+1)` reproduce the manuscript's `S_m=Σ_{ν>m}[π²(ν−1/2)²]⁻¹` exactly: `k=0` is `ν=m+1`, with no omitted or duplicated endpoint. The public theorem `1≤m → cosineTail m < 1/(9m)` is valid for every positive natural order. It does not silently impose `m≥16`; that threshold is a later corollary.

For each summand set `n=m+k≥1`; then `(n+1/2)²=n(n+1)+1/4>n(n+1)>0`, so `1/(n+1/2)² < 1/[n(n+1)] = 1/n−1/(n+1)`. The first `N` comparison terms sum exactly to `1/m−1/(m+N)`. This proves positivity and summability of the proposed series and gives `S_m≤1/(π²m)`. The pinned Mathlib theorem `Real.pi_gt_three` entails `π²>9`; with `m>0`, the final inequality is strict: `S_m<1/(9m)`. The telescoping proof is a valid exact alternative to the manuscript's midpoint-integral bound. For `m≥16`, it gives `6S_m<6/(9m)≤1/24`, with the equality at the rational endpoint `6/(9·16)=1/24` checked exactly.

I independently recomputed the separate `f(3)` ledger in rational arithmetic. Its `j=3` term is `3³/6!=3/80`; successive ratios for `j≥3` are at most `3/56`, yielding

```text
f(3) ≤ 1 + 3/2 + 3/8 + (3/80)/(1−3/56)
     = 6179/2120 < 35/12.
(6179/2120−1)/(1−1/24) = 12177/6095 = 2−13/6095 < 2.
```

The `f(3)` inequality is **not** a premise or conclusion of the proposed `cosineTail_lt_one_div_nine_mul`; it remains an independent future Lean obligation. The decimal values in the contract are explanatory only and do not replace these exact fractions.

Even with this tail lemma and `f(3)` proved, the all-order target still requires the Euler cosine/hyperbolic-cosine product link to the frozen `1/(2j)!` series, normalized Padé existence, the Schur/tableau denominator estimate `0<b_(m,j)≤S_m^j`, and disk transport to every reduced representation. The reviewed finite-range theorem already covers `1≤m≤15`; the proposed estimate is intended for the later `m≥16` argument. No complete all-order theorem is claimed.

| Reviewed input | SHA-256 |
| --- | --- |
| **`docs/lean/proofs/MF-03/ALL_ORDER_TAIL_PRE_REVIEW.md`** | **`d25c72b46df6115b75e07e92f44a6a10a9b78e333d37c0561b49eefe20eba130`** |
| Canonical `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| Source manuscript `MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56b5abf542a18ff36247b` |
| Frozen `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| Reviewed `lean-statements/NLA/Proofs/MF03/FiniteRange.lean` | `b83eadb2aa7bb33dfaf8f553be0ae16df5cab60762a90ff11cea2e609f38278a` |
| Pinned Mathlib `Analysis/Real/Pi/Bounds.lean` | `bb8dc6144292b803b2df8c31ca32d67a7ab47b50f8005b5b688d95aff1489444` |

This verdict is prior to implementation; changed contract or mathematical source bytes reopen review.
