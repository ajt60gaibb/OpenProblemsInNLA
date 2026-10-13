# TR-14 WidthBasics: independent final review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE these three elementary lemmas as partial progress toward the unchanged TR-14 target. They do not prove the ordinary-to-symmetric implication or `NLA.Statements.TR14.Target`.

The imported elaborated signatures are:

```lean
symmetricWidth_to_ordinaryWidth :
  ∀ {m n r : ℕ}, 0 < m → ∀ {H : (Fin m → Fin n) → ℂ},
    SymmetricWidth H r → OrdinaryWidth H r

ordinaryWidth_zero_iff :
  ∀ {m n : ℕ} (H : (Fin m → Fin n) → ℂ),
    OrdinaryWidth H 0 ↔ ∀ i, H i = 0

symmetricWidth_zero_iff :
  ∀ {m n : ℕ} (H : (Fin m → Fin n) → ℂ),
    SymmetricWidth H 0 ↔ ∀ i, H i = 0
```

The first proof absorbs each symmetric summand's scalar into the mode `k₀=0`, which exists under `0<m`. The product of the mode scalars is exactly that scalar; the argument also works when `r=0`, because the outer sum is empty. Both zero-width equivalences are unconditional in `m,n`: a `Fin 0` summation is empty, and the converse constructs vacuous `Fin 0` factors. In particular, they cover the frozen target's `r=0` endpoint without an extra nonzero-tensor assumption. They make no claim about the substantive implication from arbitrary ordinary factors to symmetric factors at positive width.

I imported the frozen module in a separate Lean file under pinned Lean 4.33.1, set `leancert.trust "kernel"`, printed all three elaborated declarations, and ran `#assert_trust kernel` and `#print axioms` on each. The command exited 0; each axiom set was exactly `[propext, Classical.choice, Quot.sound]`. The source has no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, or `implemented_by`. The module's own kernel assertions agree with the imported check.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/TR14/WidthBasics.lean`** | **`b32d120ca3832c5274cda96b0bc65732dbc0e0a15979acbf63a161284c985691`** |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Approved `EXACT_PROOF_PRE_REVIEW.md` | `abd73514c57e2d8c5f6a2709273a43ad282c854c8647e99855492f23052a6698` |
| Independent exact pre-review | `35f0045858ee95aead041fc86cce52dd2f061fcb804f749491762f9f69fbfe53` |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |

Changed source bytes reopen this review. No full TR-14 proof is certified by these lemmas.
