# MF-23 independent review of the block-order proof

**Reviewer:** `/root`, 9 October 2026. **Verdict:** APPROVE the local `NLA.MF23.canonical_crouzeix_proved : Target` proof and selected `NLA.MF23.canonical_crouzeix : Target` Solution wrapper as exact proofs of the [independently reviewed canonical statement](CANONICAL_STATEMENT_INDEPENDENT_REVIEW.md). An isolated Linux Comparator run is still pending.

I checked the proof after the statement review and before project integration. `Matrix.reindex` along `Equiv.prodComm (Fin n) (Fin m)` maps the upstream `(r,i),(s,j)` entry of `∑ A^k ⊗ B_k` to the canonical `(i,r),(j,s)` entry of `∑ B_k ⊗ A^k`. The source proves this equality by matrix extensionality and Kronecker entry expansion; commutativity is used only for complex scalar products. The reindexing is a `StarAlgEquiv`, and `StarAlgEquiv.norm_map` gives an equality of the exact scoped `L2Operator` norms. The final application of the pinned `complete_crouzeix` theorem retains the literal factor `2`, all positive sizes and degrees, and the unaltered full numerical-range `rangeMaximum`. There is no relaxed right side or extra premise.

The earlier bridge audit passed in the pinned Lean 4.34.1 scratch project. Packaging renamed only its final theorem to `canonical_crouzeix_proved`; `Solution.lean` then exports `canonical_crouzeix` with the same `Target` type for Comparator. The proof body and mathematical argument are unchanged. A source scan found no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `sorryAx`, or `opaque` in the local bridge, statement, or Solution. The separate Challenge contains the intentional comparison hole and is not imported by Solution. I independently reran the generated selected-Solution audit in the new source-locked project. It required `.thmInfo`, passed `#assert_trust kernel` on `NLA.MF23.canonical_crouzeix`, and printed exactly `[propext, Classical.choice, Quot.sound]` as its transitive axioms. The remaining reproducibility gate is an isolated Linux Comparator/LeanCert run.

## SHA-256 reviewed sources

| Input | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-23/README.md` | `ce65d34a504156e52e9b917419b7f3a0bf605cea219a4b627197de470ffbe324` |
| `matrix-functions-and-stability/MF-23/lean/CanonicalStatement.lean` | `9ce2eff57267fcccf4b6bf39c06754d65f8d4bf19316254cfa2a7372bfc11f81` |
| `matrix-functions-and-stability/MF-23/lean/CanonicalBridge.lean` | `94b52a868ff9c57afb248f410398bfe66acc9748c9633573f5f4946dab1ab4ef` |
| `matrix-functions-and-stability/MF-23/lean/CanonicalBridgeAudit.lean` | `4e19c5f4bd6982606f05532e2e7810ad6642288fbd439a3a140e4b43696ff34b` |
| `matrix-functions-and-stability/MF-23/lean/Solution.lean` | `a55feede620de4096686ce3aae568024b9ac18e6615b1e04646cb5e20f897f68` |
| `matrix-functions-and-stability/MF-23/lean/Challenge.lean` | `3540e233782f93d328b573b0cf0f16e2275319923583436efd26126c953553c2` |
| `matrix-functions-and-stability/MF-23/lean/comparator.json` | `ff8888a92bc53c34ad2030fff72d4b073365ed8c53b2dbf008737066784b6f11` |
| pinned upstream `Model.lean` | `3be01360e343e41c9712883d81e8845122ef13b2418640fa32c5e2fd22cdba84` |
| pinned upstream `CompleteBound.lean` | `c8f0706d92662aaca2d1a26fe7647b3719035f72177d68fbf5b490028f12e891` |
| generated `/private/tmp/MF23ProofTrustAudit.lean` | `2e9ea9bc07511f637acc2eab00e09b3987a591def3428f0cea438805130da25b` |

The upstream closure is `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Its copied files and project metadata require separate hash and CI review after integration.
