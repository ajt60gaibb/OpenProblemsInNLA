import NLA.Proofs.RE06.PseudoInverseMeasurable

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators

namespace NLA.Proofs.RE06.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery

def frobeniusSq {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  ∑ i, ∑ j, B i j ^ 2

theorem frobeniusSq_nonneg {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    0 ≤ frobeniusSq B := by
  apply Finset.sum_nonneg
  intro i _
  exact Finset.sum_nonneg (fun j _ => sq_nonneg (B i j))

theorem frobeniusSq_trace {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    frobeniusSq B = Matrix.trace (B.transpose * B) := by
  unfold frobeniusSq Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

theorem full_row_inverse_gram {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (hdet : (B * B.transpose).det ≠ 0) :
    (pseudoInverse B).transpose * pseudoInverse B = (B * B.transpose)⁻¹ := by
  have hunit : IsUnit (B * B.transpose).det := isUnit_iff_ne_zero.mpr hdet
  have hR : B * (B.transpose * (B * B.transpose)⁻¹) = 1 := by
    rw [← Matrix.mul_assoc]
    exact Matrix.mul_nonsing_inv _ hunit
  have hBP := mul_actual_eq_one_of_right_inverse B _ hR
  calc
    _ = (B.transpose * (B * B.transpose)⁻¹).transpose * pseudoInverse B :=
      congrArg (fun P => P.transpose * pseudoInverse B) (full_row_formula B hdet)
    _ = ((B * B.transpose)⁻¹).transpose * (B * pseudoInverse B) := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = (B * B.transpose)⁻¹ := by
      rw [hBP, Matrix.mul_one]
      simp only [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem full_row_frobeniusSq_trace_inverse_gram {a b : ℕ}
    (B : Matrix (Fin a) (Fin b) ℝ) (hdet : (B * B.transpose).det ≠ 0) :
    frobeniusSq (pseudoInverse B) = Matrix.trace (B * B.transpose)⁻¹ := by
  rw [frobeniusSq_trace, full_row_inverse_gram B hdet]

#assert_trust kernel full_row_inverse_gram
#assert_trust kernel full_row_frobeniusSq_trace_inverse_gram
#print axioms full_row_frobeniusSq_trace_inverse_gram
end NLA.Proofs.RE06.Pseudo
