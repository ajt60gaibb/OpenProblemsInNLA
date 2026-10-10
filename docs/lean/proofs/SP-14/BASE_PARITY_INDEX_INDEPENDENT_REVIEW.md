# SP-14 odd-section parity indexing: independent Lean source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `BaseParityIndex.lean` as a kernel-checked equivalence that lists even positions before odd positions in every section of order `2m+1`, including `m=0`. This is finite index algebra only; it does not identify Fourier coefficients, actual Toeplitz matrix blocks, or their characteristic polynomial.

`baseParityMap m` sends `Sum.inl i`, for `i:Fin(m+1)`, to position `2i`, and `Sum.inr j`, for `j:Fin m`, to position `2j+1` in `Fin(2m+1)`. These bounds are exact: the largest even position is `2m`, while the largest odd position is `2m−1` when the odd side is inhabited. The source proves injectivity by distinguishing parity and then equal values within each summand. Domain and codomain have the same finite cardinality `(m+1)+m=2m+1`, so `Equiv.ofBijective` yields `baseParityEquiv m`. At `m=0`, the domain is `Fin 1 ⊕ Fin 0`, the codomain `Fin 1`, and the sole even index maps to zero; the construction remains valid without a special hypothesis. The exported `inl` and `inr` equations record the precise maps needed for later matrix reindexing.

The theorem source contains no reindexing of a concrete Toeplitz matrix. In particular, the equivalence by itself does not establish the off-diagonal `B,C` blocks or `charpoly(T_(2m+1))`; those require the frozen Fourier coefficient identity and matrix algebra already identified in the approved actual-Toeplitz contract.

Pinned `lake build NLA.Proofs.SP14.BaseParityIndex` and a separate imported audit of the map, equivalence, both application equations, `#assert_trust kernel`, and transitive axioms passed under Lean 4.33.1. The axiom list for the equivalence is exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseParityIndex.lean`** | **`d3869fbae8425198080d1cb39e9a2ee332a957da735317ce521ec887cc827446`** |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_ACTUAL_TOEPLITZ_PRE_REVIEW.md` | `0760870797779a198c7fd16e4b1af8d06a398d9384ede2dc20c058a2881674e9` |
| `BASE_ACTUAL_TOEPLITZ_INDEPENDENT_PRE_REVIEW.md` | `19a06a06d0046bc9d7c333c84f5a115b91f798540d7e160633b973891cee9c21` |
| Independent `/private/tmp/sp14-baseparityindex-independent-audit.lean` | `c091be068e4fc160ffca6eb14d9f65d2f2bd0fe7d091b38c9af867da6a8bbb27` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or approved contract bytes reopen this review.
