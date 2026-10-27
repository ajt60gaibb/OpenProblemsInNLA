import NLA.Proofs.RE06.PseudoInverseMeasurable

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE06.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery

theorem gram_det_ne_zero_of_right_inverse {a b : ℕ}
    (B : Matrix (Fin a) (Fin b) ℝ) (R : Matrix (Fin b) (Fin a) ℝ)
    (hR : B * R = 1) : (B * B.transpose).det ≠ 0 := by
  have hBP := mul_actual_eq_one_of_right_inverse B R hR
  have hG : (B * B.transpose) *
      ((pseudoInverse B).transpose * pseudoInverse B) = 1 := by
    calc
      _ = B * (pseudoInverse B * B).transpose * pseudoInverse B := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = B * (pseudoInverse B * B) * pseudoInverse B := by rw [pseudoinverse_mul_transpose]
      _ = (B * pseudoInverse B) * (B * pseudoInverse B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBP, Matrix.mul_one]
  exact Matrix.det_ne_zero_of_right_inverse hG

theorem gram_det_ne_zero_iff_right_inverse {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (B * B.transpose).det ≠ 0 ↔ ∃ R : Matrix (Fin b) (Fin a) ℝ, B * R = 1 := by
  constructor
  · intro h
    refine ⟨B.transpose * (B * B.transpose)⁻¹, ?_⟩
    rw [← Matrix.mul_assoc]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h)
  · rintro ⟨R, hR⟩
    exact gram_det_ne_zero_of_right_inverse B R hR

theorem gram_det_ne_zero_iff_surjective {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (B * B.transpose).det ≠ 0 ↔ Function.Surjective B.mulVec := by
  rw [gram_det_ne_zero_iff_right_inverse]
  constructor
  · rintro ⟨R, hR⟩ v
    refine ⟨R.mulVec v, ?_⟩
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  · intro h
    obtain ⟨R, hR⟩ := (range_subset_iff_matrix_factor (1 : Matrix (Fin a) (Fin a) ℝ) B).mp
      (fun v _ => h v)
    exact ⟨R, hR.symm⟩

theorem measurableSet_full_row_rank (a b : ℕ) :
    MeasurableSet {B : Matrix (Fin a) (Fin b) ℝ | (B * B.transpose).det ≠ 0} := by
  have hc : Continuous (fun B : Matrix (Fin a) (Fin b) ℝ => (B * B.transpose).det) :=
    (continuous_id.matrix_mul continuous_id.matrix_transpose).matrix_det
  exact measurableSet_ne hc.measurable measurable_const

#assert_trust kernel gram_det_ne_zero_iff_surjective
#assert_trust kernel measurableSet_full_row_rank
#print axioms gram_det_ne_zero_iff_surjective
end NLA.Proofs.RE06.Pseudo
