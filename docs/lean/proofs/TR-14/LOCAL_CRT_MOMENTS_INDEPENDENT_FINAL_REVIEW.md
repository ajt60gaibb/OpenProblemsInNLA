# TR-14 CRT all-moment and Hankel transfer: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen moment-transfer module for aggregate import. It reconstructs all supplied moments and every zero-based Hankel entry from the actual monic apolar quotient; it does not assert a global tensor-width bound.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/LocalCRTMoments.lean` | `5b429dc43ff5aed6602524c41646f76018f25cd5ea2755ae9d9c132382ee52fa` |
| Exact CRT transfer contract | `d267bd05e2f9ce15bc5c76c6614e6ce66f627b6e1f6a1c235eebcb06ddbcf184` |
| Independent mathematical pre-review | `48941cc712607f82f2bcf560dd287d25f1ec92afd5246ce557bd33f59388ef00` |
| Separate imported audit `/private/tmp/tr14-local-crt-moments-independent-audit.lean` | `4b2a07784529a322f1feb3d36229a73b22b2f245470e94ac347eb89a3c49f7ca` |

The first theorem combines the actual quotient functional's all-moment identity with the audited CRT component sum and exact image of every root power. Its conclusion holds for **every** `j:Fin(D+1)`, not only the initial power-basis prefix. The second theorem discharges the all-moment premise from monic apolarity using the previously audited recurrence and quotient theorem. For `D=m*q`, `HankelIndex i` lies in `Fin(D+1)` by the frozen definition; the third theorem applies the all-moment formula and the finite product-of-powers identity to obtain each zero-based Hankel coordinate as `Σα Λ_α(∏ₖ(α+zα)^(iₖ))`. This also handles the generalized empty-mode and zero-degree endpoints, while the frozen Target later uses `m≥3` and mode size `n=q+1≥2`. No local Frobenius hypothesis is silently added to these algebraic coordinate identities.

The pinned Lean 4.33.1 direct module build passed 3,427 jobs. My separate imported LeanCert audit exited zero, checked all three public signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. The frozen source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The audited minimal-apolar Frobenius theorem supplies the required global nondegeneracy. Local Fourier term reindexing, original projective-root multiplicity correspondence, global width bounds, and the complete TR-14 Target remain separate obligations.
