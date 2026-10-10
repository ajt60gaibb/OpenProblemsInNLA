# RA-10 generic matrix/operator bridge for the frozen nuclear ideal obligation

**Status:** source-locked generic dependency precontract for independent review. It does not claim nuclear homogeneity, either ideal inequality, or Equation (14)'s numerical bound.

## Frozen definitions and pinned semantics

| Source | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/NUCLEAR_IDEAL_EQ14_PRE_REVIEW.md` | `77da0117b61b482c844382ab4893ad0553b48fce67a66d807a7f42809cdbd3ef` |
| Pinned `Mathlib/Analysis/CStarAlgebra/Matrix.lean` | Lean 4.33.1 and repository-locked Mathlib dependency |

The frozen `NuclearNorm M` sums all `n` singular values of `Matrix.toEuclideanLin M : EuclideanSpace ℝ (Fin n)→ₗ[ℝ]EuclideanSpace ℝ (Fin n)`. Under `open scoped Matrix.Norms.L2Operator`, `‖M‖` is the Euclidean induced operator norm of the same matrix. Pinned `Matrix.toEuclideanCLM` is a star-algebra equivalence, with `Matrix.coe_toEuclideanCLM_eq_toEuclideanLin` and `Matrix.cstar_norm_def`. Thus matrix multiplication and scalar multiplication are represented by composition and scaling of the underlying Euclidean operators, with exactly the same order `X*Y` ↦ `X∘Y`. This is a semantic bridge required before any attempt to prove the coefficient-one nuclear ideal property for the frozen sum of singular values.

## Exact generic claims

For every `n`, real `n×n` matrices X,Y and real scalar r, including `n=0`:

```text
toEuclideanLin (X*Y) = (toEuclideanLin X) ∘ₗ (toEuclideanLin Y),
toEuclideanLin (r • X) = r • toEuclideanLin X,
NuclearNorm (X*Y)
  = Σ_{i:Fin n} ((toEuclideanLin X) ∘ₗ (toEuclideanLin Y)).singularValues i.val,
‖X‖₂→₂ = ‖toEuclideanCLM X‖.
```

The third equality is a literal unfolding of the **frozen** nuclear definition after the first equality; it does not estimate any singular value. The fourth equality uses the scoped L2 operator norm instance, not an entrywise norm. None of these facts implies `NuclearNorm(XY)≤‖X‖ NuclearNorm Y` without additional spectral work. The pinned `SingularValues.lean` has no direct product or smul theorem, and this gate explicitly leaves those exact coefficient-one facts open.

## Proposed exact Lean declarations

Use a separate `NLA.Proofs.RA10.NuclearIdealOperatorBridge` module importing the frozen RA-10 statement and `Mathlib.Analysis.CStarAlgebra.Matrix`; write `open scoped Matrix.Norms.L2Operator`. Both operator equalities retain `LinearMap` order. The sum declaration must remain a `Fin n` sum of the pinned singular-values sequence, not a new Schatten norm.

```lean
namespace NLA.Proofs.RA10

theorem toEuclideanLin_mul_exact {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanLin (X * Y) =
      (Matrix.toEuclideanLin X).comp (Matrix.toEuclideanLin Y) := by
  ...

theorem toEuclideanLin_smul_exact {n : ℕ} (r : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanLin (r • X) = r • Matrix.toEuclideanLin X := by
  ...

theorem nuclearNorm_mul_as_operator_comp {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (X * Y) =
      ∑ i : Fin n,
        ((Matrix.toEuclideanLin X).comp (Matrix.toEuclideanLin Y)).singularValues i.val := by
  ...

theorem matrix_l2_opNorm_eq_operator_norm {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) :
    ‖X‖ = ‖Matrix.toEuclideanCLM X‖ := by
  ...

end NLA.Proofs.RA10
```

Independent review should check the composition order and right-side type, scope of the matrix norm, the exact frozen `Fin n` singular-value cutoff, scalar action, and `n=0`. After approval, implement only kernel-proved declarations and freeze for imported exact-signature/source/axiom audit. The two nuclear ideal inequalities and Equation (14)'s coefficient-one `1/(s+c)` estimate remain explicitly open.
