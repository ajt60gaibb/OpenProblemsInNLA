# TR-14 supported CRT local functionals: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen local-functional module for aggregate import. It proves exact component decomposition and inherited local Frobenius; the all-moment Hankel formula and tensor width remain open.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/LocalCRTFunctional.lean` | `fcd470c3f9b05673aa9dee6ef242c15b1b6665eafdc88b06881beebaca9582aa` |
| Exact CRT transfer contract | `d267bd05e2f9ce15bc5c76c6614e6ce66f627b6e1f6a1c235eebcb06ddbcf184` |
| Independent mathematical pre-review | `48941cc712607f82f2bcf560dd287d25f1ec92afd5246ce557bd33f59388ef00` |
| Separate imported audit `/private/tmp/tr14-local-crt-functional-independent-audit.lean` | `592e59f870aa4ec93f836596d5f002748887d40806de70eb67bc058faf60d6fc` |

The insertion `ι_α` is a complex-linear map into the product algebra with exactly one nonzero coordinate; it is not claimed to be unital. Its proved identity `ι_α(a)*v=ι_α(a*v_α)` is the componentwise multiplication required for Frobenius transfer. The local functional is exactly `Λ∘E⁻¹∘ι_α` for the audited complex-algebra CRT equivalence. Summing supported insertions reconstructs every product tuple, so the source proves `Λ(x)=Σα Λ_α((E x)_α)` for every quotient class, including an empty index type. If the global pairing is nondegenerate, an element whose local pairing vanishes against every local `b` has a supported preimage pairing to zero against every global `y`; global Frobenius makes that preimage zero, and taking its `α` coordinate gives the original element zero. No local Frobenius premise is added.

The pinned Lean 4.33.1 direct module build passed 3,426 jobs. My separate imported LeanCert audit exited zero, checked the insertion, component, decomposition, and Frobenius signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. The frozen source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

All-moment reconstruction from the actual normalized quotient functional, zero-based Hankel coordinates, original projective-root correspondence, and complete TR-14 Target remain open.
