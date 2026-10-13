import NLA.Proofs.RA10.NuclearNormTriangle
import NLA.Proofs.RA10.NuclearNormHomogeneity
import NLA.Proofs.RA10.NuclearOrthogonalConjugation
import NLA.Proofs.RA10.PinchingReflection

/-! RA-10 source Equation (8): coefficient-one nuclear contraction under
two-block orthogonal pinching, for the exact frozen singular-value sum. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA10

theorem nuclearNorm_pinch_le {n : ℕ}
    (P M : Matrix (Fin n) (Fin n) ℝ)
    (hsym : P.transpose = P) (hid : P * P = P) :
    NLA.Statements.RA10.NuclearNorm
      (P * M * P + (1 - P) * M * (1 - P)) ≤
      NLA.Statements.RA10.NuclearNorm M := by
  let U := reflection P
  have htrans : U.transpose = U := reflection_transpose P hsym
  obtain ⟨hleft, hright⟩ := reflection_orthogonal P hsym hid
  have hconj : NLA.Statements.RA10.NuclearNorm (U * M * U) =
      NLA.Statements.RA10.NuclearNorm M := by
    simpa only [htrans] using
      (nuclearNorm_orthogonal_conj U M hleft hright)
  change NLA.Statements.RA10.NuclearNorm (pinch P M) ≤
    NLA.Statements.RA10.NuclearNorm M
  calc
    NLA.Statements.RA10.NuclearNorm (pinch P M) =
        (1 / 2 : ℝ) * NLA.Statements.RA10.NuclearNorm (M + U * M * U) := by
      rw [pinch_eq_reflection_average, nuclearNorm_smul]
      norm_num [U]
    _ ≤ (1 / 2 : ℝ) *
        (NLA.Statements.RA10.NuclearNorm M +
          NLA.Statements.RA10.NuclearNorm (U * M * U)) := by
      exact mul_le_mul_of_nonneg_left (nuclearNorm_add_le M (U * M * U))
        (by norm_num)
    _ = NLA.Statements.RA10.NuclearNorm M := by rw [hconj]; ring

#assert_trust kernel nuclearNorm_pinch_le
#print axioms nuclearNorm_pinch_le

end NLA.Proofs.RA10
