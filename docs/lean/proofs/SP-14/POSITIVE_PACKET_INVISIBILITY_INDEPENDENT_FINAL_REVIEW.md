# SP-14 positive packet Fourier support and invisibility: independent Lean review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `PositivePacketInvisibility.lean` against the **revised** independently approved pre-proof contract. It proves the packet's exact all-integer Fourier support and invisibility in a frozen Toeplitz section through order `2m+1` for a **continuous** background symbol. This is one finite-section persistence component, not the final SP-14 counterexample.

The source defines `positivePacket τ m z = τ(z^(2m+1)+z^(2m+3))`, exactly the canonical `Q_m(s)=τs^m(1+s)` after `a(z)=zg(z²)`. The public Fourier theorem places coefficient `τ` at the two distinct positive integer modes `2m+1` and `2m+3` and zero at all other integers, under the frozen `1/(2π)` interval integral and negative exponential phase. It uses the reviewed circle-mode orthogonality theorem and continuous finite terms. The packet-only formula remains unconditional in `τ,m,k`.

The Toeplitz theorem's elaborated signature includes `ha : Continuous a` and `hn : n≤2m+1`, exactly repairing the earlier totalized-integral issue without changing the frozen `OriginalConjecture` or `Target`. Its private additivity lemma explicitly proves both interval integrands continuous and therefore interval-integrable before applying `intervalIntegral.integral_add`. For `i,j:Fin n`, the row-minus-column frequency is at most `n−1≤2m`, so it cannot be either packet mode. Equality follows entrywise. At `m=0,n=1`, the only diagonal frequency is zero; at `n=0`, the extensional proof is vacuous. There is no claim about an arbitrary noncontinuous background or about the restoring negative packet.

Pinned `lake build NLA.Proofs.SP14.PositivePacketInvisibility` and a separate imported LeanCert audit of the definition, exact theorem signatures, `#assert_trust kernel`, and transitive axioms exited successfully under Lean 4.33.1. Both public theorems list exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/PositivePacketInvisibility.lean`** | **`90df55a41491c60d442df3679d1808c2c77a66d8e66fe8dbffe940151c3c8d1f`** |
| Revised `POSITIVE_PACKET_INVISIBILITY_PRE_REVIEW.md` | `1379412b7a537ca32bec5d86f74f5896a6f192857e60b27b6337393d08677519` |
| `POSITIVE_PACKET_INVISIBILITY_REVISED_INDEPENDENT_PRE_REVIEW.md` | `b1c7d74ad987c9cc1ff0df1071bbff062c34771fd8114fa7dc4c13c81d8dcd8b` |
| `BaseFourierMode.lean` | `6744fba387ed60bbf05377478f20612f59a47fc5503f553e400dbce1d88cbbfe` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Independent `/private/tmp/sp14-positivepacket-independent-audit.lean` | `c75b3ea2ef6e34278c9af720b1e525d64ef185029c5bf855692ccc134f50045e` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or approved contract bytes reopen this review. Future negative-packet invisibility, all-stage persistence, final nonextension, and empirical gap remain separate obligations.
