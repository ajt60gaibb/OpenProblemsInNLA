import NLA.Proofs.RA10.NuclearIdealPointwiseLeft

/-! RA-10: the sharp left nuclear ideal inequality for the frozen sum of
all singular values. The right ideal inequality and Eq. (14) remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem nuclearIdeal_left {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (X * Y) ≤
      ‖X‖ * NLA.Statements.RA10.NuclearNorm Y := by
  unfold NLA.Statements.RA10.NuclearNorm
  calc
    (∑ i : Fin n, (Matrix.toEuclideanLin (X * Y)).singularValues i.val) ≤
        ∑ i : Fin n, ‖X‖ * (Matrix.toEuclideanLin Y).singularValues i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact singularValues_left_mul_le X Y i
    _ = ‖X‖ * ∑ i : Fin n, (Matrix.toEuclideanLin Y).singularValues i.val := by
      rw [Finset.mul_sum]

#assert_trust kernel nuclearIdeal_left
#print axioms nuclearIdeal_left

end NLA.Proofs.RA10
