import NLA.Proofs.RA10.NuclearSingularValuesTranspose

/-! RA-10: transpose invariance of the exact frozen all-singular-value
nuclear norm. The operator-norm transpose and right ideal gates follow. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem nuclearNorm_transpose {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm M.transpose =
      NLA.Statements.RA10.NuclearNorm M := by
  unfold NLA.Statements.RA10.NuclearNorm
  apply Finset.sum_congr rfl
  intro i _
  exact singularValues_transpose_eq M i

#assert_trust kernel nuclearNorm_transpose
#print axioms nuclearNorm_transpose

end NLA.Proofs.RA10
