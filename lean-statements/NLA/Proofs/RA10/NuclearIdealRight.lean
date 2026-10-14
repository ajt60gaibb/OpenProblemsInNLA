import NLA.Proofs.RA10.NuclearIdealLeft
import NLA.Proofs.RA10.NuclearNormTranspose
import NLA.Proofs.RA10.NuclearOperatorNormTranspose

/-! RA-10: the sharp right nuclear ideal inequality for the frozen
all-singular-value norm and scoped Euclidean operator norm. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem nuclearIdeal_right {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (X * Y) ≤
      NLA.Statements.RA10.NuclearNorm X * ‖Y‖ := by
  calc
    NLA.Statements.RA10.NuclearNorm (X * Y) =
        NLA.Statements.RA10.NuclearNorm (X * Y).transpose :=
      (nuclearNorm_transpose (X * Y)).symm
    _ = NLA.Statements.RA10.NuclearNorm (Y.transpose * X.transpose) := by
      rw [Matrix.transpose_mul]
    _ ≤ ‖Y.transpose‖ * NLA.Statements.RA10.NuclearNorm X.transpose :=
      nuclearIdeal_left Y.transpose X.transpose
    _ = NLA.Statements.RA10.NuclearNorm X * ‖Y‖ := by
      rw [l2OpNorm_transpose, nuclearNorm_transpose]
      ring

#assert_trust kernel nuclearIdeal_right
#print axioms nuclearIdeal_right

end NLA.Proofs.RA10
