# RA-10 frozen nuclear norm under left orthogonal multiplication

**Status:** source-locked mathematical and exact-signature precontract for independent review. No Lean implementation or proof is claimed. This is one staged dependency for the approved nuclear pinching and nuclear ideal gates, not Equation (8), Equation (14), or the full `RA-10` Target.

## Source lock and role

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/NUCLEAR_PINCHING_GATE_PRE_REVIEW.md` | `23d850db3f312e04a30d732e1e9f030f04b80f5c7eff1584c4711a3aa435ffa1` |
| `docs/lean/proofs/RA-10/NUCLEAR_IDEAL_EQ14_PRE_REVIEW.md` | `77da0117b61b482c844382ab4893ad0553b48fce67a66d807a7f42809cdbd3ef` |

The archived solution uses two-sided orthogonal invariance for its nuclear pinching step. The frozen `NLA.Statements.RA10.NuclearNorm M` is **exactly** `∑ i : Fin n, (Matrix.toEuclideanLin M).singularValues i.val`. This contract isolates the left half of orthogonal invariance while retaining the actual all-`n` singular-value definition. It neither replaces that norm with the L2 operator norm nor uses an unproved nuclear ideal inequality.

## Exact mathematical statement

For every natural dimension `n`, every real `n×n` matrices `U,X`, and the sole orthonormal-column hypothesis `UᵀU=I`, prove

```text
NuclearNorm (U X) = NuclearNorm X.
```

`X` is arbitrary: no symmetry, positivity, invertibility, rank, commutation, or spectral-gap assumption. The statement includes singular `X`, tied or zero singular values, and `n=0`. In dimension zero the sum is empty and the unique matrices satisfy the hypothesis. The hypothesis on `U` is sufficient because left multiplication leaves the Gram matrix unchanged; a separate `UUᵀ=I` hypothesis is unnecessary for this direction. No index is dropped or reselected.

## Exact proof obligation and pinned semantics

Let `T_M = Matrix.toEuclideanLin M` on `EuclideanSpace ℝ (Fin n)`. Pinned `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, real `conjTranspose=transpose`, and the exact multiplication bridge give

```text
T_(UX)† T_(UX)
  = T_X† T_U† T_U T_X
  = T_X† T_(UᵀU) T_X
  = T_X† T_X.
```

Equivalently, `(UX)ᵀ(UX)=XᵀX`; use whichever path genuinely kernel-proves the same operator equality. In pinned `SingularValues.lean`, `LinearMap.singularValues_fin` identifies the value at `i.val` with the square root of the ordered eigenvalue of this Gram operator. Therefore every corresponding value at the *same* `i : Fin n` is equal, including ties and zero values, and summing over the original `Fin n` gives the conclusion. This argument requires no SVD choice, maximum, trace surrogate, or dimension-dependent estimate.

## Proposed exact Lean declaration

Implement in a separate `NLA.Proofs.RA10.NuclearOrthogonalLeft` module after independent approval, importing the frozen RA-10 statement and audited multiplication bridge:

```lean
namespace NLA.Proofs.RA10

theorem nuclearNorm_orthogonal_left {n : ℕ}
    (U X : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.transpose * U = 1) :
    NLA.Statements.RA10.NuclearNorm (U * X) =
      NLA.Statements.RA10.NuclearNorm X := by
  ...

end NLA.Proofs.RA10
```

The theorem must have no added right-orthogonality or positivity premise. It proves only the left multiplication identity. Right multiplication, two-sided conjugation, nuclear triangle, coefficient-one ideal inequalities, the selected pinching contraction, and the frozen `Target` remain open until separately kernel-proved.

## Review and verification gate

Independent pre-review must check the frozen `NuclearNorm` index cutoff, left/right order in `T_U ∘ T_X`, the adjoint/transpose orientation, the exact single hypothesis `UᵀU=I`, and dimension zero. After approval, direct-check with the pinned Lean toolchain and LeanCert kernel, freeze the source SHA and exact public signature, and request a separate imported source/signature/axiom audit before aggregate import. No `sorry`, `admit`, custom axiom, `native_decide`, unsafe declaration, or computation in place of the all-dimensional proof.
