# RA-10 exact L2 operator norm under real transpose

**Status:** source-locked mathematical/numerical and public-signature precontract for independent review before implementation. It is a narrow dependency of the separately approved right nuclear ideal route and does not claim Eq. (14) or the RA-10 Target.

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/NUCLEAR_IDEAL_RIGHT_PRE_REVIEW.md` | `d76b887276af293d7f2c6ff99b3bffe9b35f7ee343e2ffe1fb43cc1e81ba1194` |
| `lean-statements/NLA/Proofs/RA10/NuclearIdealOperatorBridge.lean` | `27a30c33bb8b758013f99e1775c01d0515d90b3a4fe62ceb60d28fc9d8cf5ced` |
| pinned Mathlib `Analysis/CStarAlgebra/Matrix.lean` | `79518c9e51c4d0cf4083ab69a9ac7a2817305b48db1fe6f25ae1d678e12ce223` |

With **`open scoped Matrix.Norms.L2Operator`**, prove for all dimensions `n : ℕ` and arbitrary real square `M : Matrix (Fin n) (Fin n) ℝ` the exact coefficient-one equality `‖M.transpose‖ = ‖M‖`. This is the **Euclidean induced operator norm**, not the frozen nuclear norm or Frobenius norm. It includes `Fin 0` and zero matrices. The pinned `Matrix.l2_opNorm_conjTranspose M` states `‖Mᴴ‖=‖M‖` for the scoped norm. For real entries, `Matrix.conjTranspose_eq_transpose_of_trivial` identifies `Mᴴ=Mᵀ`; no complex conjugation or inverse assumption enters.

Proposed exact public declaration in a separate `NLA.Proofs.RA10.NuclearOperatorNormTranspose` module:

```lean
open scoped Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem l2OpNorm_transpose {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖M.transpose‖ = ‖M‖ := by
  ...

end NLA.Proofs.RA10
```

Independent review must verify the scoped norm instance, real transpose conversion, exact coefficient and all-dimension quantifier, before Lean implementation. Require direct pinned LeanCert kernel and separate imported exact-signature/source/axiom audit. No `sorry`, `admit`, custom axiom, `native_decide`, or unsafe declaration.
