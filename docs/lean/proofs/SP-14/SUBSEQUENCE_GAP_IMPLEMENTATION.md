# SP-14 conditional subsequence-gap lemma: implementation record

**Author:** `/root/sp14_base_proof`, 9 October 2026. This record concerns one conditional implication only. The SP-14 counterexample and unconditional `Target` remain unproved in Lean.

The pre-proof mathematical contract in `SUBSEQUENCE_GAP_PRE_REVIEW.md` was independently approved in `SUBSEQUENCE_GAP_INDEPENDENT_PRE_REVIEW.md` before implementation. The Lean theorem `NLA.Proofs.SP14.target_of_subsequence_gap` in `lean-statements/NLA/Proofs/SP14/SubsequenceGap.lean` has exactly the reviewed parameters and assumptions, and concludes the frozen `NLA.Statements.SP14.Target`. It applies a hypothetical `OriginalConjecture` to the supplied symbol and test, composes its full-sequence limit with the strictly increasing selected orders, takes real parts, and contradicts the eventual positive gap.

The direct pinned check was:

```text
Lean toolchain: leanprover/lean4:v4.33.1
Command (from lean-statements/): lake env lean NLA/Proofs/SP14/SubsequenceGap.lean
Exit: 0
LeanCert: #assert_trust kernel target_of_subsequence_gap passed
#print axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, declared axiom, or witness theorem hidden in this conditional lemma. Its `hgap` premise has to be proved from the source's actual Toeplitz multiplicities and finite bound; its symbol/test, analytic nonextension, and zero canonical integral premises also remain to be established.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `docs/lean/proofs/SP-14/SUBSEQUENCE_GAP_PRE_REVIEW.md` | `01babfcb793e4bbf51ba810fad419a485a7b7c49d8bbb09fabe616c8d4c33f78` |
| `docs/lean/proofs/SP-14/SUBSEQUENCE_GAP_INDEPENDENT_PRE_REVIEW.md` | `d86b7edb2749391fe2acb89af543ede260f82beb7f595556e7e78e67360a5b2f` |
| `lean-statements/NLA/Proofs/SP14/SubsequenceGap.lean` | `63d3c4eb341e6c0e33898b003652df015f753a34181d0526dc107642044cf71d` |
