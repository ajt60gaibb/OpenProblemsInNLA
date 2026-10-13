# TR-14 primary-root quotient shift: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen primary shift module for aggregate import. This is the local algebra constituent of CRT, not the global product equivalence.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/LocalCRTShift.lean` | `acdf8a8aa508cd7b74edd2a9c6128968ac183c45f81262451b694c28e7e22a3a` |
| Exact CRT transfer contract | `d267bd05e2f9ce15bc5c76c6614e6ce66f627b6e1f6a1c235eebcb06ddbcf184` |
| Independent mathematical pre-review | `48941cc712607f82f2bcf560dd287d25f1ec92afd5246ce557bd33f59388ef00` |
| Separate imported audit `/private/tmp/tr14-local-crt-shift-independent-audit.lean` | `c893862148fd7f09f6be65e174a6fffb0b6737ac73051b4f52d521fb5382628a` |

The source defines the primary factor `(X−C α)^ℓ` and maps its quotient to `LocalTruncated ℓ = ℂ[z]/z^ℓ` by sending the quotient root to `α+z`. This respects the factor relation because `z^ℓ=0`. Its inverse maps the local nilpotent generator to the primary quotient root minus `α`, which satisfies the local nilpotence relation. Both composite algebra homomorphisms are identities by their generator images. The resulting `≃ₐ[ℂ]` preserves complex scalars and has the exact reviewed root-image identity. It works for every `ℓ`, including zero; the later CRT application uses the previously proved positive multiplicities.

The pinned Lean 4.33.1 direct module build passed 3,424 jobs. My separate imported LeanCert audit exited zero, checked the algebra-map, equivalence, and root-image signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The product CRT equivalence, local functional transfer, all-moment reconstruction, projective-root correspondence, and complete TR-14 Target remain open.
