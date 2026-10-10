# SP-14 positive packet invisibility: revised independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE revised frozen `POSITIVE_PACKET_INVISIBILITY_PRE_REVIEW.md` (SHA-256 below) for implementation. It resolves the totalized-integral gap identified in the [first independent review](POSITIVE_PACKET_INVISIBILITY_INDEPENDENT_PRE_REVIEW.md) by requiring `ha : Continuous a` **only** for the background-dependent Toeplitz invisibility lemma. The packet's exact all-integer Fourier formula stays unconditional. This is an intermediate lemma; the frozen `SP14.Target` and original conjecture are unchanged, and the latter already quantifies over continuous symbols.

The transformed source packet `Q_m(s)=τs^m(1+s)` is exactly `positivePacket τ m z = τ(z^(2m+1)+z^(2m+3))`. The frozen real-interval Fourier convention and audited circle-mode orthogonality put coefficients `τ` at precisely those positive modes and zero at every other integer mode. The revised proof route explicitly obtains interval integrability from continuity before using `intervalIntegral.integral_add`; it no longer asserts linearity for arbitrary nonintegrable backgrounds. For a section `n≤2m+1`, every row-minus-column frequency has magnitude at most `n−1≤2m`, so neither packet mode enters. The boundary cases `m=0,n=1` and empty `n=0` remain covered. The optional `Q_m(-1)=0` endpoint algebra is correct and separate from the Fourier argument.

This theorem is only a finite-section persistence fact for **positive** packets. It supplies no negative-correction invisibility, stage-selection certificate, final symbol nonextension, eigenvalue multiplicity, compact test separation, or empirical subsequence gap. No packet Lean source existed at this revised pre-review.

| Reviewed input | SHA-256 |
| --- | --- |
| **Revised `POSITIVE_PACKET_INVISIBILITY_PRE_REVIEW.md`** | **`1379412b7a537ca32bec5d86f74f5896a6f192857e60b27b6337393d08677519`** |
| Original contract reviewed for the gap | `9479dc2c3f4d31c471cf2944e79b437bec1f1408e2103b40b662e4b41b4e85ab` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BaseFourierMode.lean` | `6744fba387ed60bbf05377478f20612f59a47fc5503f553e400dbce1d88cbbfe` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Pinned Mathlib `IntervalIntegral/Basic.lean` | `93908eb0c771ba8edcb47537dfe1a40e98a1545be9d427c1eb9823d44decdcd5` |

Changed source bytes reopen this review.
