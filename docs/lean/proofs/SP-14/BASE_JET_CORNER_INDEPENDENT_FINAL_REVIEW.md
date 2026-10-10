# SP-14 selected-block cofactor: independent Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `BaseJetCorner.lean` for the exact generic finite-matrix identity. This module is partial and does not prove an actual Toeplitz jet formula or `SP14.Target`.

The candidate source was written before its separate mathematical pre-review. It remained unimported and frozen at the stated hash while the [independent contract review](BASE_JET_CORNER_INDEPENDENT_PRE_REVIEW.md) checked the exact assertion and endpoints. I then read the complete source and compared its theorem signature and proof with that approved contract before integration.

For arbitrary `G : (m+1)×(m+1)`, the source defines the selected product `C*B` by rows `0,…,m−1` and columns `1,…,m`. Its private minor lemma proves entrywise that deleting the last row and first column of `G²−(t+1)U` gives `C*B−(t+1)I_m`. The adjugate cofactor contributes `(-1)^m`; negating the `m×m` minor to obtain the characteristic-polynomial matrix contributes the same sign. Their product is positive. The theorem therefore equates the selected block's characteristic polynomial at `t+1` to the exact adjugate corner for **every** `m`, including the `1×1`/empty-block `m=0` case, without an invertibility or triangularity premise. It uses no surrogate Fourier coefficient or modified Toeplitz section. The later source-specific identification of `G` with the actual frozen Fourier blocks and the explicit base jet remain open.

I independently ran a separate **imported** LeanCert audit under pinned Lean 4.33.1. It elaborated the exact public theorem signature, ran `#assert_trust kernel`, and printed its transitive axioms. The audit exited 0 and depends only on `[propext, Classical.choice, Quot.sound]`. The frozen source contains no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseJetCorner.lean`** | **`4e9d3861ed43fe36db4065dc91370635a1a26c1faa99a52a8b84b5511c659f6c`** |
| Approved `BASE_JET_CORNER_PRE_REVIEW.md` | `959d50629c5f5d4e99bae58972f28d7db5da9f3810627cf0afdb3e959b4ac561` |
| Independent mathematical pre-review | `9671aaae98bc0faaa8e3696f9cb67dfc3793f842700eaa405bc8ff61f924504f` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Imported `/private/tmp/sp14-basejetcorner-independent-audit.lean` | `c9351d711792c99471fa65d95ed5f5fb47afb83e1c8c42dbc6bbe91bbb2a7a32` |

Changed source or contract bytes reopen this review.
