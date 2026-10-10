# SP-14 actual Toeplitz parity blocks: independent Lean source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `BaseParityBlocks.lean` as the exact all-`m` parity-block theorem **conditional on** `BaseFourierPattern a`. The theorem uses the frozen integral-defined `Toeplitz` matrix. It does not establish the Fourier pattern for the proposed base symbol, its characteristic polynomial, or the final SP-14 counterexample.

The elaborated theorem is

```lean
NLA.Proofs.SP14.toeplitz_base_parity_blocks
  (a : Circle → ℂ) (m : ℕ)
  (hpattern : NLA.Proofs.SP14.BaseFourierPattern a) :
  Matrix.reindex (baseParityEquiv m).symm (baseParityEquiv m).symm
      (NLA.Statements.SP14.Toeplitz a (2 * m + 1)) =
    Matrix.fromBlocks 0 (baseB m) (baseC m) 0
```

`BaseFourierPattern a` requires every even integer Fourier coefficient to vanish and gives every odd coefficient at frequency `1−2p`: it is `baseCoeff p.toNat` for `p≥0` and zero for `p<0`. The variable `p` ranges over **all integers**, so these clauses cover every frequency without a truncated range or substituted discrete Fourier transform. The `FourierCoefficient` referred to is the frozen real-interval integral with factor `1/(2π)` and exponential `e^(−ikt)`; `Toeplitz` takes row frequency minus column frequency. No continuity assumption on arbitrary `a` is needed for this conditional algebraic implication because the hypothesis supplies the exact values of those integrals.

The source's four matrix-entry cases have the correct orientation. Even row `2i`, odd column `2j+1` gives frequency `1−2(j+1−i)` and therefore entry `c_(j+1−i)` when `i≤j+1`, precisely `(baseB m) i j`. Odd row `2i+1`, even column `2j` gives `1−2(j−i)` and entry `c_(j−i)` when `i≤j`, precisely `(baseC m) i j`. Both same-parity blocks have even frequency and are zero. The reindexing uses the previously proved genuine equivalence `Fin(m+1) ⊕ Fin m ≃ Fin(2m+1)`, with all even positions first. For `m=0`, the odd summand and both rectangular blocks are empty; the sole diagonal entry is the stipulated zero-frequency coefficient, so the theorem covers the endpoint.

I independently reran the pinned `lake build NLA.Proofs.SP14.BaseParityBlocks` and a separate imported audit that checked the elaborated signature, asserted LeanCert `kernel` trust, and printed transitive axioms. Both exited successfully under Lean 4.33.1. The theorem's axiom list is exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseParityBlocks.lean`** | **`06ef7ef23d4ea068188c011c680c2c4a43ee8ef6d8a0a8c23dfbac943dc4c5f2`** |
| `lean-statements/NLA/Proofs/SP14/BaseCB.lean` | `4d08f355b18258aaee4a2a2a7c7546ffee8b13c81d746a8582aea105c7509e79` |
| `lean-statements/NLA/Proofs/SP14/BaseParityIndex.lean` | `d3869fbae8425198080d1cb39e9a2ee332a957da735317ce521ec887cc827446` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_ACTUAL_TOEPLITZ_PRE_REVIEW.md` | `0760870797779a198c7fd16e4b1af8d06a398d9384ede2dc20c058a2881674e9` |
| Independent `/private/tmp/sp14-baseparityblocks-independent-audit.lean` | `2095dcd466a86f1fbbf141a48ac28713fcd28f5170357ab2ba85b825ae923fd5` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or statement bytes reopen this review. The analytic proof of `BaseFourierPattern BaseSymbol`, off-diagonal polynomial identity, and characteristic-polynomial bridge remain separate obligations.
