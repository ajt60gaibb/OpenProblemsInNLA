import NLA.Proofs.RA10.NuclearIdealOperatorBridge

/-! RA-10: exact real-transpose invariance of the scoped Euclidean
operator norm, distinct from the frozen nuclear norm. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem l2OpNorm_transpose {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖M.transpose‖ = ‖M‖ := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.l2_opNorm_conjTranspose M

#assert_trust kernel l2OpNorm_transpose
#print axioms l2OpNorm_transpose

end NLA.Proofs.RA10
