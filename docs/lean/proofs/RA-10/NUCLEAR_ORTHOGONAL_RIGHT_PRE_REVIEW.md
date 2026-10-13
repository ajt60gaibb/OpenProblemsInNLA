# RA-10 frozen nuclear norm under right orthogonal multiplication

**Status:** source-locked mathematical and exact-signature precontract for independent review. No Lean implementation or proof is claimed. The exact left-orthogonal stage has a frozen direct-check source, but its separate imported audit is pending. This right stage remains unimplemented until independent approval.

## Source lock and role

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/NUCLEAR_PINCHING_GATE_PRE_REVIEW.md` | `23d850db3f312e04a30d732e1e9f030f04b80f5c7eff1584c4711a3aa435ffa1` |
| `docs/lean/proofs/RA-10/NUCLEAR_ORTHOGONAL_LEFT_PRE_REVIEW.md` | `626b9d76a21d7aa0dd759a9758adf87be4c9e450408406d9e3d19a09dd0cfff8` |
| `lean-statements/NLA/Proofs/RA10/NuclearOrthogonalLeft.lean` | `55e08063ce32da702db380e9d82315517b65d28082c0504f33919bc4f91146ba` |

The archived RA-10 solution's nuclear pinching argument requires two-sided orthogonal conjugation invariance. The frozen `NLA.Statements.RA10.NuclearNorm M` sums **all** `n` singular values of `Matrix.toEuclideanLin M` at indices `i.val` for `i : Fin n`. This contract isolates the right multiplication half; it does not alter the norm, assert pinching, or assume an ideal inequality.

## Exact mathematical statement

For every natural `n`, arbitrary real square matrices `X,U`, and the sole orthonormal-row hypothesis `UUᵀ=I`, prove

```text
NuclearNorm (X U) = NuclearNorm X.
```

The matrix `X` need not be symmetric, PSD, invertible, full rank, or commuting with `U`. Tied and zero singular values remain included; `n=0` is valid with empty singular-value sums. No basis re-selection or positive-rank cutoff is allowed. A separate `UᵀU=I` hypothesis is unnecessary for the exact right multiplication equality in finite square dimension.

## Exact characteristic-polynomial obligation

Put `G=XᵀX`. The Gram matrix of `XU` is `Uᵀ G U`, preserving the noncommutative order. In pinned Mathlib, `Matrix.charpoly_mul_comm` for square matrices and the hypothesis `UUᵀ=I` give the coefficient-one identity

```text
charpoly(Uᵀ G U)
  = charpoly((Uᵀ G) U)
  = charpoly(U (Uᵀ G))
  = charpoly((UUᵀ) G)
  = charpoly G.
```

This charpoly equality is transferred to the matching Gram **Euclidean linear operators** using the pinned matrix/linear-map characteristic-polynomial correspondence. Pinned `LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff` then gives equality of the **ordered** real Gram eigenvalue functions at each same `i : Fin n`, including repeated and zero roots. Finally `LinearMap.singularValues_fin` gives equal square roots at `i.val`, and summing over the frozen `Fin n` gives the theorem. The proof cannot infer the result from equality of singular-value multisets without establishing the same ordered indexing, nor replace the nuclear norm with an operator norm.

## Proposed exact Lean declaration

Implement in a separate `NLA.Proofs.RA10.NuclearOrthogonalRight` module after independent approval. It may import the audited operator bridge and left stage for helper APIs, but may not assume its conclusion as an extra premise:

```lean
namespace NLA.Proofs.RA10

theorem nuclearNorm_orthogonal_right {n : ℕ}
    (X U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U * U.transpose = 1) :
    NLA.Statements.RA10.NuclearNorm (X * U) =
      NLA.Statements.RA10.NuclearNorm X := by
  ...

end NLA.Proofs.RA10
```

This is the right half of orthogonal invariance. A later theorem may combine the left/right facts under both `UᵀU=I` and `UUᵀ=I` to reach the already approved two-sided conjugation signature. Nuclear triangle, coefficient-one ideal bounds, pinching contraction, and the frozen `Target` remain open.

## Review and verification gate

Independent pre-review must check the original nuclear norm cutoff, `XU` multiplication order, the exact `UUᵀ` hypothesis, cyclic charpoly step, ordered eigenvalue pairing including ties and zeros, and `Fin 0`. After approval, direct-check in pinned LeanCert kernel mode; freeze SHA and public signature for a separate imported source/axiom audit before aggregate import. No `sorry`, `admit`, custom axiom, `native_decide`, unsafe declaration, or per-order computation.
