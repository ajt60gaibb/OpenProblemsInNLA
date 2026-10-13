# RA-10 sharp right nuclear ideal via transpose

**Status:** source-locked mathematical, indexing, and numerical precontract for independent review. No Lean implementation or right ideal proof is claimed. This is a dependency for source Equation (14), not the full RA-10 Target.

## Sources and exact objects

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/NUCLEAR_IDEAL_EQ14_PRE_REVIEW.md` | `77da0117b61b482c844382ab4893ad0553b48fce67a66d807a7f42809cdbd3ef` |
| pinned Mathlib `Analysis/InnerProductSpace/SingularValues.lean` | `ce8193fcd5d226845a71f66b8ca7ad385358916a6e0e688745410ac412ed5c81` |
| pinned Mathlib `Analysis/Matrix/Spectrum.lean` | `1ad47effa0a5fbc373ebb6cf52a6b85a66b25d3c5a86394f3dd5932ffbfc3afe` |
| pinned Mathlib `LinearAlgebra/Matrix/Charpoly/Basic.lean` | `584eb12d39eacb591155c98cfa2089479d88cfdea8eb5f31ba5ed687de200a9a` |
| pinned Mathlib `Analysis/InnerProductSpace/Adjoint.lean` | `f28b5896638f712605265a69ffe4469f1f42e1b78b10ade0844738aeecd2b2a2` |

Under `open scoped Matrix.Norms.L2Operator`, `‖Y‖` is the Euclidean induced operator norm. The frozen `NuclearNorm M` sums **every** `Fin n` singular value of `Matrix.toEuclideanLin M` at `i.val`. The precise coefficient-one right ideal theorem for arbitrary real square matrices is

```text
NuclearNorm (X*Y) ≤ NuclearNorm X * ‖Y‖₂→₂.
```

No positivity, rank, nonzero-dimension, invertibility, normality, or commutativity assumption is present. It includes ties, zero singular values, and `Fin 0`.

## Exact transpose route

First prove for every `i:Fin n` that

```text
singularValues(toEuclideanLin (Mᵀ), i.val)
  = singularValues(toEuclideanLin M, i.val).
```

The two squared lists are the ordered eigenvalues of `(Mᵀ)ᵀMᵀ=MMᵀ` and `MᵀM`. These Gram matrices are real symmetric PSD and have exactly the same characteristic polynomial by pinned `Matrix.charpoly_mul_comm` for square `M,Mᵀ`. The pinned `Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff` recovers equality of the indexed matrix eigenvalue functions from that charpoly equality. The `sq_singularValues_fin` and matrix/linear-map ordered Gram bridge must use the **same zero-based `Fin n` index**, including the explicit `sortedHermitianIndex` conversion; mere equality of unordered multisets is insufficient. Nonnegative singular values turn equality of squares into equality of values. Summing over `Fin n` gives exactly `NuclearNorm M.transpose=NuclearNorm M`.

The matrix transpose corresponds to the Euclidean adjoint and preserves its operator norm, so prove `‖M.transpose‖=‖M‖` under the same L2 scope. Pinned `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` specializes to the real transpose; the pinned adjoint norm isometry and matrix L2 operator-norm bridge then identify the exact matrix norms.

Finally, using the separately reviewed coefficient-one **left** ideal theorem, apply it to `Y.transpose * X.transpose`, then use `(X*Y).transpose=Y.transpose*X.transpose`, both transpose invariances, and commutativity of real scalar multiplication:

```text
NuclearNorm (X*Y)
 = NuclearNorm (YᵀXᵀ)
 ≤ ‖Yᵀ‖₂→₂ * NuclearNorm (Xᵀ)
 = NuclearNorm X * ‖Y‖₂→₂.
```

No factor of `n`, `2`, or an inverse is introduced. Do not replace the frozen nuclear norm with a Frobenius or matrix operator norm. The left ideal inequality must itself be kernel proved before the last stage.

## Proposed staged public signatures

```lean
namespace NLA.Proofs.RA10

theorem singularValues_transpose_eq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (Matrix.toEuclideanLin M.transpose).singularValues i.val =
      (Matrix.toEuclideanLin M).singularValues i.val := by
  ...

theorem nuclearNorm_transpose {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm M.transpose =
      NLA.Statements.RA10.NuclearNorm M := by
  ...

end NLA.Proofs.RA10
```

```lean
open scoped Matrix.Norms.L2Operator
namespace NLA.Proofs.RA10

theorem nuclearIdeal_right {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (X * Y) ≤
      NLA.Statements.RA10.NuclearNorm X * ‖Y‖ := by
  ...

end NLA.Proofs.RA10
```

An exact public transpose operator-norm helper may be separately proposed and reviewed if needed. Independent review must verify every source lock, the Gram product order, charpoly/eigenvalue **index** equality, nonnegative square roots, the exact scoped norm, and the final product orientation before implementation. Each stage then needs direct pinned LeanCert kernel proof and a separate imported exact-signature/source/axiom audit. No `sorry`, `admit`, custom axiom, `native_decide`, unsafe declaration, or numerical enumeration.
