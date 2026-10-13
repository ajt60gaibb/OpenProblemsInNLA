# SP-14 rectangular off-diagonal characteristic polynomial: independent Lean review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `BaseOffdiagonalCharpoly.lean` against the approved pre-proof contract. It proves a generic complex-polynomial identity for **every** `m : ℕ`, including `m=0`, and arbitrary rectangular `B,C`. It remains a finite algebra component, not the analytic base-symbol theorem or the SP-14 counterexample.

The independently elaborated declaration is

```lean
NLA.Proofs.SP14.charpoly_offdiagonal_succ (m : ℕ)
  (B : Matrix (Fin (m + 1)) (Fin m) ℂ)
  (C : Matrix (Fin m) (Fin (m + 1)) ℂ) :
  (Matrix.fromBlocks 0 B C 0).charpoly =
    Polynomial.X * (C * B).charpoly.comp (Polynomial.X ^ 2)
```

The product is `C*B`, an `m×m` matrix; hence the right side has degree `1+2m`, matching the full block size. The source makes no invertibility, normality, diagonalizability, Fourier, or nonzero-spectral-parameter hypothesis. At `m=0`, the lower block and both rectangular blocks are empty, so the formula reads `X = X·1`.

The proof works inside `ℂ[X]`. It writes the characteristic matrix as `A=[[XI,−B],[−C,XI]]`, then multiplies by `N=[[I,B],[0,XI]]`. The upper-right block cancels because scalar `X` commutes through `B`; the lower-right block is `X²I−CB`. Block triangular determinants give `det(A)·X^m = X^(m+1)·χ_(CB)(X²)`. A proved polynomial-ring regularity lemma cancels `X^m`, including when `m=0`. Thus equality is a **polynomial identity at `X=0` as well**, with no division by a spectral value or extension from a punctured set. The private composition lemma identifies `χ_(CB)(X²)` with `det(X²I−CB)` via the characteristic-matrix and determinant ring-homomorphism identities.

I independently reran the pinned `lake build NLA.Proofs.SP14.BaseOffdiagonalCharpoly` and a separate imported LeanCert audit of the exact signature, `#assert_trust kernel`, and transitive axiom list. Both exited successfully under Lean 4.33.1. The axiom list is exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseOffdiagonalCharpoly.lean`** | **`c503becdb5f9c1cae1da8724c744ebbdf3937316e5536702eaac865de3b88e33`** |
| Imported `lean-statements/NLA/Proofs/SP14/BaseParityBlocks.lean` | `06ef7ef23d4ea068188c011c680c2c4a43ee8ef6d8a0a8c23dfbac943dc4c5f2` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_OFFDIAGONAL_CHARPOLY_PRE_REVIEW.md` | `c8913cf163d7c31f5927e218d8bbd370a869a80f222e1db6ad55fce10c33fbcd` |
| `BASE_OFFDIAGONAL_CHARPOLY_INDEPENDENT_PRE_REVIEW.md` | `77c706b8078ab4ad664b66ede4b1888b73f8e64a8aba590b55fee62d56cb5a74` |
| Independent `/private/tmp/sp14-baseoffdiagonal-independent-audit.lean` | `85ec6be6adbcd05e8fe2676f774421b57d6ed2e965a3340b0efcd417044c653e` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or approved contract bytes reopen this review. The Fourier pattern for the actual base symbol, the characteristic-polynomial assembly for its frozen Toeplitz matrix, and the final counterexample remain separate obligations.
