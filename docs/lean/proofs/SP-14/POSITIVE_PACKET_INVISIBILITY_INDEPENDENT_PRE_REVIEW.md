# SP-14 positive packet invisibility: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** MATHEMATICAL SIGNATURE APPROVED; **proof contract needs correction before implementation**. The frequencies, cutoff, and endpoint scopes match the frozen Toeplitz convention and canonical source. The sentence asserting unrestricted linearity of the frozen Fourier integral for arbitrary background `a` is false for Mathlib's totalized Bochner interval integral without integrability hypotheses.

The source packet `Q_m(s)=τs^m(1+s)` under `a(z)=zg(z²)` becomes exactly `τz^(2m+1)+τz^(2m+3)`. The independently certified integer-mode theorem gives its frozen Fourier coefficient as the sum of the two Kronecker terms for every `k:ℤ`, including negative `k`. For `i,j:Fin n` and `n≤2m+1`, the row-minus-column frequency satisfies `|i−j|≤n−1≤2m`, strictly below both positive packet modes. Thus its contribution vanishes on every entry of the `n×n` section. At `m=0,n=1`, the only frequency is zero; at `n=0`, both matrices are empty. The optional `Q_m(-1)=0` endpoint is correct. This packet result is only future finite-section persistence and does not prove final-symbol nonextension or a subsequence gap.

**Required proof-route repair.** `intervalIntegral.integral_add` in pinned Mathlib requires `IntervalIntegrable` for **both** addends; `integral_undef` sets a nonintegrable interval integral to zero. Consequently `FourierCoefficient (a+packet) k = FourierCoefficient a k + FourierCoefficient packet k` is not a general identity for arbitrary `a`; at a packet mode it can fail when the background phase is nonintegrable. The proposed invisibility theorem can still retain arbitrary `a` because the packet's integral is **zero at the relevant frequencies**. Prove its integrability and zero integral, then split on interval-integrability of the background phase. In the integrable case, use `integral_add`. In the nonintegrable case, adding the integrable packet leaves the sum nonintegrable (otherwise subtracting the packet would make the background integrable); `integral_undef` makes both relevant integrals zero. This supplies the unrestricted equality without invoking false blanket linearity. An alternative, sufficient for the eventual continuous final symbol, is a separately frozen intermediate theorem with `Continuous a`; that changes this proposed helper signature and would need a new review. The unchanged SP-14 `Target` must not acquire such a premise.

| Reviewed input | SHA-256 |
| --- | --- |
| **`POSITIVE_PACKET_INVISIBILITY_PRE_REVIEW.md`** | **`9479dc2c3f4d31c471cf2944e79b437bec1f1408e2103b40b662e4b41b4e85ab`** |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BaseFourierMode.lean` | `6744fba387ed60bbf05377478f20612f59a47fc5503f553e400dbce1d88cbbfe` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Pinned Mathlib `IntervalIntegral/Basic.lean` | `93908eb0c771ba8edcb47537dfe1a40e98a1545be9d427c1eb9823d44decdcd5` |

No Lean packet source was present at this review. Revised contract bytes must be independently checked before implementation.
