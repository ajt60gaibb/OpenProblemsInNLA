# SP-14 subsequence-gap lemma: independent Lean source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE the frozen `SubsequenceGap.lean` as a kernel-checked proof of exactly the conditional bridge approved before implementation. It does not construct the Thalhammer counterexample and does not prove the unconditional `NLA.Statements.SP14.Target`.

The theorem `NLA.Proofs.SP14.target_of_subsequence_gap` has the exact pre-reviewed binders: continuous `a : Circle→ℂ`, no inner or outer extension, continuous compactly supported `F : ℂ→ℂ`, `Canonical a F=0`, strictly increasing `n : ℕ→ℕ`, `δ>0`, and an eventual lower bound `δ≤(Empirical a F (n j)).re`. Its conclusion is the frozen `Target := ¬ OriginalConjecture`, not a new or narrower target. The theorem assumes a positive gap rather than deriving it from source multiplicities; this is explicit in its signature.

The proof assumes `OriginalConjecture`, instantiates its complete universal statement with the supplied `a,F`, and obtains the full natural-order complex limit to zero. `hn.tendsto_atTop` composes that limit along genuine increasing Toeplitz orders. Continuity of the complex real-part map gives convergence of the selected real parts to zero. The positive `δ` then yields an eventual strict bound `<δ`, contradicting the supplied eventual bound `≥δ`. The `Eventually` conjunction is inhabited on `atTop` for naturals. No finite-order `θ/2` inequality is asserted; the source's exact `⌊θm⌋/(2m+1)` bound and its limit, along with the symbol and test construction, remain separate future obligations.

I directly compiled the frozen source under pinned Lean 4.33.1, ran `lake build NLA.Proofs.SP14.SubsequenceGap`, and imported it into a separate audit that checked its elaborated signature, `#assert_trust kernel`, and transitive axioms. All passed. The axiom list is exactly `[propext, Classical.choice, Quot.sound]`. A proof-escape scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/SubsequenceGap.lean`** | **`63d3c4eb341e6c0e33898b003652df015f753a34181d0526dc107642044cf71d`** |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `SUBSEQUENCE_GAP_PRE_REVIEW.md` | `01babfcb793e4bbf51ba810fad419a485a7b7c49d8bbb09fabe616c8d4c33f78` |
| `SUBSEQUENCE_GAP_INDEPENDENT_PRE_REVIEW.md` | `d86b7edb2749391fe2acb89af543ede260f82beb7f595556e7e78e67360a5b2f` |
| Canonical `eigenvalues-and-inverse-problems/SP-14/README.md` | `9d0c6376080838ea50e8736cb4249276c06a528479fb9c9f565cc7747a485075` |
| Approved `docs/lean/statements/SP-14/NUMERICAL_TARGETS.md` | `f507ad236fc7c9e9547ce23ebe74ddffac84872d66648cc8b543ff89d6f39efc` |
| Independent `/private/tmp/sp14-subsequence-gap-independent-audit.lean` | `2eadda8f1d751a5a783a9d450bd05914ee6d77db76a686ac7cc1a74d8a9fd717` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or contract bytes reopen the corresponding review.
