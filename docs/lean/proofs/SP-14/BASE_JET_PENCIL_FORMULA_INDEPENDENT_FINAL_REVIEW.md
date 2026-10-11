# SP-14 actual base-jet pencil formula: independent Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `BaseJetPencilFormula.lean` for the exact finite jet polynomial of the actual exterior base plus one complete restored negative packet. This is a base-model identity, not the perturbed-background construction or `NLA.Statements.SP14.Target`.

I read the complete 490-line source and compared the elaborated public theorem with the independently approved mathematical contract. The source defines `E` from the same `baseJetG` correction entries established by the audited Fourier-to-Toeplitz bridge. Under `2q≤m+1`, it proves `E²=0`, commutation with the base upper triangular matrix, and the exact pencil `G_v²-(1+t)U=I-tU+2G₀E`. It constructs the finite geometric inverse of `I-tU`, proves a two-sided explicit inverse for the complete pencil, and proves its determinant is one. The already reviewed generic cofactor identity then identifies its upper-right adjugate entry with the characteristic polynomial of the **actual** selected odd Toeplitz blocks.

The upper-right entry of the geometric inverse is `t^m`. In the correction term, the source proves `W²` has coefficient `(k+1)t^k`, multiplies by the exact half-binomial base matrix, and selects the packet shift `m-d`. This yields precisely `-2∑_{d<q}v_d∑_{k≤d}(k+1)c_{d-k}t^k`, including the source's index reversal. Polynomial extensionality turns the pointwise result into the public equality for `oddJetPolynomial (baseJetSymbol m q v) m` at every `m,q,v` satisfying the bound. No matrix surrogate replaces the frozen Fourier coefficient or Toeplitz definition; the theorem includes `m=q=0`, arbitrary `q=0`, and the equality-bound `2q=m+1` cases.

I independently imported the frozen module under pinned Lean 4.33.1, checked the exact public definitions and theorem signature, ran LeanCert `#assert_trust kernel`, and printed its transitive axioms. The audit exited 0 and reports only `propext`, `Classical.choice`, and `Quot.sound`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseJetPencilFormula.lean`** | **`b3f114a5fe3a986fec2a6e13d827b2b399f86c69efcf37a0bbe3bce03f313f50`** |
| Approved `BASE_JET_PENCIL_FORMULA_PRE_REVIEW.md` | `34382ee1010794845f95e1d3138d30e2b59202d10a1025f0630d4834c9a98957` |
| Independent mathematical pre-review | `dd925f11d74a170dd2d1b1aba4d7f80bd69da182f3881d2b64160f36874360d6` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Imported `/private/tmp/sp14-basejetpencil-independent-audit.lean` | `f887f4c91b36fa034059439dc160841961ccb2ebf5de42d701e2a531050b0913` |

Changed source or contract bytes reopen this review. The separately approved real-solve assembly is the next finite gate; it must identify the actual coefficient map and derivative before the base-model vector existence can be claimed.
