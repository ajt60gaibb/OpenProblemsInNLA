# SP-14 actual base-jet Fourier matrix: independent Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE the frozen `BaseJetFourierMatrix.lean` for the exact selected Fourier coefficients and the two actual odd Toeplitz blocks. This is a partial result; it does not calculate the corrected jet polynomial, select correction vectors, or prove `NLA.Statements.SP14.Target`.

I read the full source after its freeze and compared its elaborated public signatures with the independently approved pre-proof contract. The source defines the actual exterior base plus the complete restored negative packet. It expands the raw packet into circle modes of frequency `1+2(d-m)` and the restoring term into modes `1-2(m+1+r)`, then uses the frozen interval-integral Fourier coefficient and previously reviewed circle-mode orthogonality. For every integer `p≤m`, the restoring modes miss frequency `1-2p`; the raw modes contribute exactly when `p=m-d`. The source retains the raw term and does not claim that the full restored packet is invisible. Its proof of global even-frequency vanishing uses the reviewed odd-support results.

The matrix-entry bridge uses `p=j-i` and `2q≤m+1` to justify the natural subtraction `m-d`. The `oddB` frequency is `2i-(2j+1)=1-2((j+1)-i)`, so it selects columns `Fin.succ`; the `oddC` frequency is `(2i+1)-2j=1-2(j-i)`, so it selects rows `Fin.castSucc`. These are the frozen row-minus-column Toeplitz entries. The public statements cover `q=0`, `m=0`, and negative integer `p`; no finite numerical sample substitutes for the universal identities.

I separately imported the frozen module under pinned Lean 4.33.1 and ran LeanCert `#assert_trust kernel` for each public theorem, checked their exact elaborated signatures, and printed their transitive axioms. The audit exited 0. Each report contains only `propext`, `Classical.choice`, and `Quot.sound`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseJetFourierMatrix.lean`** | **`03ded74b3244a27cad27e829dd634b6a54a32f17b4a3e468640f1372da8285bd`** |
| Approved `BASE_JET_FOURIER_MATRIX_PRE_REVIEW.md` | `fdb3b1ffc3daa48c80a49c03bc86777d865012eedff16b747414c3e45ffc1cbb` |
| Independent mathematical pre-review | `3c008e333c7a698c2d8b8f01779490c22d14fd3ddffafc0e8f6f703de10c2965` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Imported `/private/tmp/sp14-basejetfourier-independent-audit.lean` | `cfe62ad32f3c6c1168bf9431cf923604d5e8c6a1efa0aaa86954b3e313366625` |

Changed source or contract bytes reopen this review.
