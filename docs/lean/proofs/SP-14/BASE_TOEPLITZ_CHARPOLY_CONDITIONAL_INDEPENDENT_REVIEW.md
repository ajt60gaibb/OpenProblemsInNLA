# SP-14 conditional actual Toeplitz characteristic polynomial: independent Lean review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `BaseToeplitzCharpolyConditional.lean` against its independently approved pre-proof contract. It proves the exact characteristic polynomial of every odd section of the **frozen integral-defined Toeplitz matrix**, conditional on the exact `BaseFourierPattern a`. It does not establish that pattern for the proposed base symbol or prove the final SP-14 counterexample.

The independently elaborated signature is

```lean
NLA.Proofs.SP14.toeplitz_base_charpoly_of_fourier_pattern
  (a : Circle → ℂ) (m : ℕ)
  (hpattern : NLA.Proofs.SP14.BaseFourierPattern a) :
  (NLA.Statements.SP14.Toeplitz a (2 * m + 1)).charpoly =
    Polynomial.X * (Polynomial.X ^ 2 - 1) ^ m
```

The proof reindexes that actual Toeplitz matrix by the previously certified even/odd equivalence and uses `Matrix.charpoly_reindex`, so characteristic-root multiplicities are retained. It rewrites the reindexed matrix to `[[0,baseB],[baseC,0]]` using the reviewed Fourier-pattern theorem. The generic rectangular identity then yields `X·charpoly(baseC*baseB)(X²)`, with the correct `C*B` orientation and a polynomial identity valid at `X=0`. The certified finite identities `baseC*baseB=baseBlock` and `charpoly(baseBlock)=(X−1)^m` give `X·(X²−1)^m` by composition. No normality, diagonalizability, or hidden eigenbasis assumption appears. At `m=0`, the formula is `X` for the one-by-one zero Toeplitz section; `m=1` gives `X³−X`.

Pinned `lake build NLA.Proofs.SP14.BaseToeplitzCharpolyConditional` and a separate imported LeanCert audit of the exact signature, kernel trust, and transitive axioms exited successfully under Lean 4.33.1. The axiom list is exactly `[propext, Classical.choice, Quot.sound]`. The source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseToeplitzCharpolyConditional.lean`** | **`1d3f3c01161ad3ba6aaadcd2603ee6b042978f43a48e88a4962292df3e96476c`** |
| `BASE_TOEPLITZ_CHARPOLY_CONDITIONAL_PRE_REVIEW.md` | `34e2e4cc1699748eabf86589b8ad6de09434d8c8a28fb00fb8c038cd234e5d2c` |
| `BASE_TOEPLITZ_CHARPOLY_CONDITIONAL_INDEPENDENT_PRE_REVIEW.md` | `f9e57c62b586e12ad96664a13ac1af6e48d43ab19722fcf700880328c4e53803` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BaseParityBlocks.lean` | `06ef7ef23d4ea068188c011c680c2c4a43ee8ef6d8a0a8c23dfbac943dc4c5f2` |
| `BaseOffdiagonalCharpoly.lean` | `c503becdb5f9c1cae1da8724c744ebbdf3937316e5536702eaac865de3b88e33` |
| `BaseCB.lean` | `4d08f355b18258aaee4a2a2a7c7546ffee8b13c81d746a8582aea105c7509e79` |
| `BaseBlockCharpoly.lean` | `603dcc3f95f21c6d3c7646b47f1d280996a81ff95e813d82c31541ef9d10db7f` |
| Independent `/private/tmp/sp14-basetoeplitzconditional-independent-audit.lean` | `2dad452927a31751bf4f2cbd77801896d4f1a44b646fe2ed51bc61f21de7da11` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or approved contract bytes reopen this review. The analytic exterior-branch Fourier identification and the final symbol's two-sided nonextension, test separation, and subsequence gap remain separate obligations.
