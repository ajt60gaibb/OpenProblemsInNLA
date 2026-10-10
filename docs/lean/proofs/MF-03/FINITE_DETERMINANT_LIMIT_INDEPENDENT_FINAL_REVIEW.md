# MF-03 finite determinant limits: independent final review

**Independent mathematical/source reviewer:** `/root/sp14_base_proof`, 10 October 2026. **Imported signature/kernel auditor:** `/root`. **Verdict:** APPROVE the frozen determinant definitions and fixed-size limits for aggregate import. Tableau identities and determinant positivity remain open.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/FiniteDeterminantLimit.lean` | `dae4fe36fa8483141b5b96e76f4a7dc58a30f2d508bb405ea58ef015413577d7` |
| Exact mathematical precontract `FINITE_DETERMINANT_LIMIT_PRE_REVIEW.md` | `6d742a8373b8b36b5235d8d6708a7ad67d6ff9f6a6c4caa50eeee4acaef4aa93` |
| Independent pre-review `FINITE_DETERMINANT_LIMIT_INDEPENDENT_PRE_REVIEW.md` | `3d741b6a0773d4adb3d22388970c4d5b5ee8bc725672041cc6486bb4bb587127` |
| Separate imported audit `/private/tmp/mf03-finite-determinant-limit-independent-audit.lean` | `fc48fe39b9bb9dee03377a9b7d18476ba18639a41dfb52ec17ff8d4ea69aa310` |

The independent reviewer checked all four **real** determinant definitions against the approved Schur–Padé contract: rectangle entry `e_(m+c−r)` and augmented entry `e_(m+1_{r<j}+c−r)`, with finite `e_N` or original infinite `e` as appropriate. Since `r<m`, natural subtraction is faithful to the intended nonnegative index. The zero-row identities hold for every `N,m`, and both determinant limits follow from the reviewed entrywise coefficient convergence and continuity of the fixed finite determinant polynomial. The proof includes `m=0`, `j=0`; the augmented limit is actually shown for every `j`, stronger than its reviewed `j≤m` surface.

The pinned Lean 4.33.1 module build passed 8,715 jobs. A separate imported audit reconstructed all four exact definitions, both zero-row identities, and both public limit signatures, reran LeanCert `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. A source scan found no proof escape. The theorem does not establish a dual Jacobi–Trudi identity, positivity, or the full MF-03 Target. Changed source bytes require a new review.
