import NLA.Proofs.RE05.OrthonormalFamily

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix

/-- The actual leverage formula is exactly a sum of matrix Gram products. -/
theorem leverage_eq_sum_gram {n q : ℕ} (P : Basis n q) :
    leverage P = ∑ j : Fin (q + 1),
      orthonormalMember P j * (orthonormalMember P j).transpose := by
  ext i k
  simp [leverage, Matrix.sum_apply, Matrix.mul_apply]

theorem leverage_symmetric {n q : ℕ} (P : Basis n q) : (leverage P).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i k
  simp [leverage, mul_comm]

/-- Positivity holds for the literal fold outputs even outside independence. -/
theorem leverage_posSemidef {n q : ℕ} (P : Basis n q) : (leverage P).PosSemidef := by
  rw [leverage_eq_sum_gram]
  apply Matrix.posSemidef_sum
  intro j _
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (orthonormalMember P j)

#assert_trust kernel leverage_eq_sum_gram
#assert_trust kernel leverage_symmetric
#assert_trust kernel leverage_posSemidef
#print axioms leverage_posSemidef
end NLA.Proofs.RE05
