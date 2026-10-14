import NLA.Proofs.RA10.NuclearOrthogonalLeft
import NLA.Proofs.RA10.NuclearOrthogonalRight

/-! RA-10: exact two-sided orthogonal conjugation invariance of the frozen
all-singular-value nuclear norm. Nuclear triangle, pinching, ideal bounds,
and the final Target remain open. -/

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA10

theorem nuclearNorm_orthogonal_conj {n : ℕ}
    (U M : Matrix (Fin n) (Fin n) ℝ)
    (hleft : U.transpose * U = 1) (_hright : U * U.transpose = 1) :
    NLA.Statements.RA10.NuclearNorm (U * M * U.transpose) =
      NLA.Statements.RA10.NuclearNorm M := by
  calc
    NLA.Statements.RA10.NuclearNorm ((U * M) * U.transpose) =
        NLA.Statements.RA10.NuclearNorm (U * M) := by
      apply nuclearNorm_orthogonal_right (U * M) U.transpose
      simpa only [Matrix.transpose_transpose] using hleft
    _ = NLA.Statements.RA10.NuclearNorm M :=
      nuclearNorm_orthogonal_left U M hleft

#assert_trust kernel nuclearNorm_orthogonal_conj
#print axioms nuclearNorm_orthogonal_conj

end NLA.Proofs.RA10
