# MF-03 cosine elementary coefficient transfer: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen coefficient-transfer module for aggregate import. It identifies all elementary coefficients of the actual infinite cosine product with the factorial wave coefficients. It does not prove all-order Padé denominator bounds or the full MF-03 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/CosineCoefficientTransfer.lean` | `b17175f8a9ed18507e98beffe08cb7d02fb802380437155aafb518c0dc05da60` |
| Exact coefficient-transfer contract | `8ba96613cfc09c64cc8b4d49c5b9d79986a21c63374b96d8c78f66db7d24528f` |
| Independent mathematical pre-review | `7cce290b938742c2c4f4c9b21a1045886a6ae566667713ebc24e7bb7e188c2a2` |
| Separate imported audit `/private/tmp/mf03-cosine-coefficient-transfer-independent-audit.lean` | `f4742403f4601f2b8be0a4a037ced00cd08dbe421da522f28153e58c4dd9b83e` |

The coefficient definition is a real `tsum` over finite subsets of the zero-based factors `cosineFactor (k+1)`, grouped by exact cardinality. Positivity and summability of the factors give absolute summability of finite-subset products. An explicit equivalence to the cardinality fibers and summable sigma rearrangement expand the actual infinite product into `Σ e_j z^j`; this remains valid at zeros of individual factors. The zero-cardinality fiber has the empty product. The previous all-complex cosine-product identity equates this sum with the factorial wave series. The source then proves both scalar formal multilinear series have positive convergence radius and invokes analytic power-series uniqueness, rather than inferring coefficient equality from function values without a uniqueness theorem. It yields `e_j = 1/(2j)!` for every `j`, including zero, with the correct one-based source to zero-based factor shift.

The pinned Lean 4.33.1 direct module build passed 8,713 jobs. My separate imported LeanCert audit exited zero, checked the exact coefficient definition and both public theorem signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The Schur/tableau denominator estimate, all-order normalized pair existence, large-order unconditional disk step, and complete MF-03 Target remain open.
