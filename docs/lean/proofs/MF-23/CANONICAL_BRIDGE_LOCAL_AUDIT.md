# MF-23 canonical block-order bridge: local kernel audit

**Prepared:** 2026-10-09 by `/root/mf23_canonical_bridge`.
**Independent statement review:**
[`CANONICAL_STATEMENT_INDEPENDENT_REVIEW.md`](CANONICAL_STATEMENT_INDEPENDENT_REVIEW.md)
approved the exact local target before this proof was implemented.

## What the proof establishes

`CanonicalBridge.lean` proves the theorem
`NLA.MF23.canonical_crouzeix_proved : NLA.MF23.Target` without adding hypotheses.
`Solution.lean` exports the selected theorem
`NLA.MF23.canonical_crouzeix : NLA.MF23.Target` by applying this proof.
`Target` is the independently reviewed all-size, all-finite-degree,
constant-two inequality with the canonical block order
`Σ B_k ⊗ A^k`. The proof uses a `StarAlgEquiv` induced by reindexing a
square matrix along an index equivalence. The C-star norm-preservation
theorem gives the exact Euclidean operator-norm equality. Entrywise
expansion and scalar multiplication commutativity show that reindexing
`Σ A^k ⊗ B_k` by `Equiv.prodComm` yields `Σ B_k ⊗ A^k`. Applying the
pinned external `OAI.DirectCrouzeix.complete_crouzeix` then proves the
constant-two bound. This argument does not use pointwise numerical-range
relaxation or a changed norm.

## Exact local verification

The proof was elaborated against the byte-identical 42 direct-proof modules
from `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a` in
`/private/tmp/mf23-verification-fr05`, with Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and LeanCert
`7f91b6eb3567437f6cfac03ed279706603ee22f4`. The pre-existing
`BUILD_FEASIBILITY.md` records the pinned external proof build.

The following commands exited 0 in the self-contained repository project.
The `lake build Challenge Solution` run covered 8,970 jobs. The final command
uses the generated audit source from the shared harness and checks the
selected `Solution` theorem:

```text
lake build Challenge Solution
lake build LeanCert.Tactic.Verification
lake env lean CanonicalBridgeAudit.lean
lake env lean /private/tmp/MF23ProofTrustAudit.lean
```

The audit sets `leancert.trust` to `"kernel"` and runs `#assert_trust kernel`
on both `OAI.DirectCrouzeix.complete_crouzeix` and the bridged internal
`NLA.MF23.canonical_crouzeix_proved`; the generated harness audit checked
the selected `NLA.MF23.canonical_crouzeix` theorem constant. All transitive
`#print axioms` results were exactly
`[propext, Classical.choice, Quot.sound]`. The successful checks establish
a genuine local Lean proof term for the canonical local target. They do not
constitute the repository's isolated Linux Comparator
receipt; a committed project with the upstream source closure and a compatible
Lean 4.34.1 verifier profile is still needed for that gate.

## SHA-256 source lock

| Input | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-23/README.md` | `ce65d34a504156e52e9b917419b7f3a0bf605cea219a4b627197de470ffbe324` |
| `matrix-functions-and-stability/MF-23/lean/CanonicalStatement.lean` | `9ce2eff57267fcccf4b6bf39c06754d65f8d4bf19316254cfa2a7372bfc11f81` |
| `matrix-functions-and-stability/MF-23/lean/CanonicalBridge.lean` | `94b52a868ff9c57afb248f410398bfe66acc9748c9633573f5f4946dab1ab4ef` |
| `matrix-functions-and-stability/MF-23/lean/CanonicalBridgeAudit.lean` | `4e19c5f4bd6982606f05532e2e7810ad6642288fbd439a3a140e4b43696ff34b` |
| `matrix-functions-and-stability/MF-23/lean/Solution.lean` | `a55feede620de4096686ce3aae568024b9ac18e6615b1e04646cb5e20f897f68` |
| generated selected-theorem `ProofTrustAudit.lean` | `2e9ea9bc07511f637acc2eab00e09b3987a591def3428f0cea438805130da25b` |
| pinned upstream `Model.lean` | `3be01360e343e41c9712883d81e8845122ef13b2418640fa32c5e2fd22cdba84` |
| pinned upstream `CompleteBound.lean` | `c8f0706d92662aaca2d1a26fe7647b3719035f72177d68fbf5b490028f12e891` |

The proof body has not yet received a second independent code review. No
canonical README, ID registry entry, or upstream source was edited.
