import NLA.Proofs.RA10.NuclearTraceDualUpper
import NLA.Proofs.RA10.NuclearTraceDualAttains

/-! RA-10: coefficient-one triangle inequality for the exact frozen sum of
all Euclidean singular values in every real square dimension. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA10

theorem nuclearNorm_add_le {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (M + N) ≤
      NLA.Statements.RA10.NuclearNorm M + NLA.Statements.RA10.NuclearNorm N := by
  obtain ⟨U, hleft, hright, hatt⟩ :=
    nuclearNorm_trace_orthogonal_attains (M + N)
  calc
    NLA.Statements.RA10.NuclearNorm (M + N) =
        Matrix.trace (U.transpose * (M + N)) := hatt.symm
    _ = Matrix.trace (U.transpose * M) + Matrix.trace (U.transpose * N) := by
      rw [Matrix.mul_add, Matrix.trace_add]
    _ ≤ NLA.Statements.RA10.NuclearNorm M +
        NLA.Statements.RA10.NuclearNorm N :=
      add_le_add
        (nuclearNorm_trace_orthogonal_le U M hleft hright)
        (nuclearNorm_trace_orthogonal_le U N hleft hright)

#assert_trust kernel nuclearNorm_add_le
#print axioms nuclearNorm_add_le

end NLA.Proofs.RA10
