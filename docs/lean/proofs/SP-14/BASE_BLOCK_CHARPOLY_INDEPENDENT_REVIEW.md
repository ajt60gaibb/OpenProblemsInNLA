# SP-14 unit lower-bidiagonal block: independent Lean source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `BaseBlockCharpoly.lean` as the exact finite-matrix characteristic-polynomial component of the approved base-symbol route. It does **not** prove that this block equals the actual `C*B` product, identify the Toeplitz Fourier matrix, establish the base symbol's all-order characteristic polynomial, or prove the final SP-14 `Target`.

The definition `baseBlock m : Matrix (Fin m) (Fin m) ℂ` has entry one exactly when the row equals the column or is its immediate successor, and zero otherwise. Thus it is the `m×m` unit **lower** bidiagonal matrix predicted in the approved block calculation. The theorem `baseBlock_charpoly (m)` states `(baseBlock m).charpoly = (X−1)^m` for every natural `m`, including `m=0`. At zero, the matrix has empty index type and both sides are the unit polynomial; no positivity hypothesis is hidden.

The proof checks that the transpose is upper triangular, uses `Matrix.charpoly_transpose`, then applies `Matrix.charpoly_of_isUpperTriangular` and the fact that every diagonal entry is one. This derives the characteristic polynomial without invoking diagonalizability or an eigenvalue enumeration. The source has no assertion that the explicit `baseBlock` is already the product of the actual even/odd Toeplitz blocks; that identity and the odd-block determinant factorization remain necessary next steps.

Pinned `lake build NLA.Proofs.SP14.BaseBlockCharpoly` and a separate imported audit of the elaborated type, `#assert_trust kernel`, and `#print axioms` all passed under Lean 4.33.1. The theorem's transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseBlockCharpoly.lean`** | **`603dcc3f95f21c6d3c7646b47f1d280996a81ff95e813d82c31541ef9d10db7f`** |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_ODD_CHARPOLY_PRE_REVIEW.md` | `2d065496f7d7a4e4abc84005b801ec3891c0089f57e28f849c79c858521c666a` |
| `BASE_ODD_CHARPOLY_INDEPENDENT_PRE_REVIEW.md` | `f7a63e4782b5c29f27fbdac58ffe1ee7e0d517827492a33a1816e37339d375c1` |
| Independent `/private/tmp/sp14-baseblockcharpoly-independent-audit.lean` | `e1a65f8139f54fc583c8917f05971abd7834c452c3d14d6131ad84d0aae323d3` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or approved contract bytes reopen this review.
