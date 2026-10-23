import NLA.Proofs.PF05.PositiveTopology

/-! Quantitative coercivity of actual real two-by-two positive definite
aggregates. The explicit determinant/trace constant bounds every entry of a
congruence matrix by the trace of its actual congruence image. This supplies
the boundedness input for a later closed-orbit proof; it proves no PF-05 Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.PF05.PositiveCoercivity

open Matrix
open scoped BigOperators

abbrev Sym2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Vec2 := Fin 2 → ℝ

/-- The actual determinant/trace ratio of a positive definite matrix is positive. -/
theorem det_div_trace_pos (P : Sym2) (hP : P.PosDef) : 0 < P.det / P.trace :=
  div_pos hP.det_pos hP.trace_pos

/-- An exact sum-of-two-squares identity gives an explicit quadratic-form
coercivity bound, with no assumed spectral lower-bound constant. -/
theorem det_div_trace_qform_lower (P : Sym2) (hP : P.PosDef) (v : Vec2) :
    (P.det / P.trace) * ((v 0) ^ 2 + (v 1) ^ 2) ≤ v ⬝ᵥ (P *ᵥ v) := by
  have hsym : P 1 0 = P 0 1 := (Matrix.isHermitian_iff_isSymm.mp hP.1).apply 0 1
  have hidentity :
      P.trace * (v ⬝ᵥ (P *ᵥ v)) - P.det * ((v 0) ^ 2 + (v 1) ^ 2) =
        (P 0 0 * v 0 + P 0 1 * v 1) ^ 2 +
          (P 0 1 * v 0 + P 1 1 * v 1) ^ 2 := by
    simp only [Matrix.trace_fin_two, Matrix.det_fin_two, dotProduct, Matrix.mulVec,
      Fin.sum_univ_two, hsym]
    ring
  have hbound : P.det * ((v 0) ^ 2 + (v 1) ^ 2) ≤ P.trace * (v ⬝ᵥ (P *ᵥ v)) := by
    nlinarith [sq_nonneg (P 0 0 * v 0 + P 0 1 * v 1),
      sq_nonneg (P 0 1 * v 0 + P 1 1 * v 1)]
  calc
    (P.det / P.trace) * ((v 0) ^ 2 + (v 1) ^ 2) =
        (P.det * ((v 0) ^ 2 + (v 1) ^ 2)) / P.trace := by ring
    _ ≤ v ⬝ᵥ (P *ᵥ v) := (div_le_iff₀ hP.trace_pos).mpr (by nlinarith)

/-- Coercivity of the actual matrix congruence, in explicit squared coordinates. -/
theorem det_div_trace_congruence_lower (P : Sym2) (hP : P.PosDef) (S : Sym2) :
    (P.det / P.trace) *
        ((S 0 0) ^ 2 + (S 1 0) ^ 2 + (S 0 1) ^ 2 + (S 1 1) ^ 2) ≤
      (S.transpose * P * S).trace := by
  have h0 := det_div_trace_qform_lower P hP ![S 0 0, S 1 0]
  have h1 := det_div_trace_qform_lower P hP ![S 0 1, S 1 1]
  have htrace : (S.transpose * P * S).trace =
      (![S 0 0, S 1 0] ⬝ᵥ (P *ᵥ ![S 0 0, S 1 0])) +
        (![S 0 1, S 1 1] ⬝ᵥ (P *ᵥ ![S 0 1, S 1 1])) := by
    simp [Matrix.trace_fin_two, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Fin.sum_univ_two]
    ring
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [htrace]
  nlinarith

/-- Every actual entry is bounded by the actual congruence trace, uniformly
with the same fixed positive coercivity constant. -/
theorem det_div_trace_entry_sq_lower (P : Sym2) (hP : P.PosDef) (S : Sym2)
    (i j : Fin 2) :
    (P.det / P.trace) * (S i j) ^ 2 ≤ (S.transpose * P * S).trace := by
  have hsum : (S i j) ^ 2 ≤
      (S 0 0) ^ 2 + (S 1 0) ^ 2 + (S 0 1) ^ 2 + (S 1 1) ^ 2 := by
    fin_cases i <;> fin_cases j <;> dsimp <;>
      nlinarith [sq_nonneg (S 0 0), sq_nonneg (S 1 0), sq_nonneg (S 0 1), sq_nonneg (S 1 1)]
  exact (mul_le_mul_of_nonneg_left hsum (det_div_trace_pos P hP).le).trans
    (det_div_trace_congruence_lower P hP S)

#assert_trust kernel det_div_trace_pos
#assert_trust kernel det_div_trace_qform_lower
#assert_trust kernel det_div_trace_congruence_lower
#assert_trust kernel det_div_trace_entry_sq_lower
#print axioms det_div_trace_entry_sq_lower

end NLA.Proofs.PF05.PositiveCoercivity
