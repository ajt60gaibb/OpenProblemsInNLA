import NLA.Proofs.RE06.PseudoInverseUnique

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE06.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery

theorem mul_actual_eq_one_of_right_inverse {a b : ℕ}
    (B : Matrix (Fin a) (Fin b) ℝ) (R : Matrix (Fin b) (Fin a) ℝ)
    (hR : B * R = 1) : B * pseudoInverse B = 1 := by
  calc
    B * pseudoInverse B = (B * pseudoInverse B) * (B * R) := by rw [hR, Matrix.mul_one]
    _ = (B * pseudoInverse B * B) * R := by simp only [Matrix.mul_assoc]
    _ = B * R := by rw [mul_pseudoinverse_mul]
    _ = 1 := hR

theorem actual_mul_eq_one_of_left_inverse {a b : ℕ}
    (B : Matrix (Fin a) (Fin b) ℝ) (L : Matrix (Fin b) (Fin a) ℝ)
    (hL : L * B = 1) : pseudoInverse B * B = 1 := by
  calc
    pseudoInverse B * B = (L * B) * (pseudoInverse B * B) := by rw [hL, Matrix.one_mul]
    _ = L * (B * pseudoInverse B * B) := by simp only [Matrix.mul_assoc]
    _ = L * B := by rw [mul_pseudoinverse_mul]
    _ = 1 := hL

theorem full_row_formula {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (hdet : (B * B.transpose).det ≠ 0) :
    pseudoInverse B = B.transpose * (B * B.transpose)⁻¹ := by
  have hunit : IsUnit (B * B.transpose).det := isUnit_iff_ne_zero.mpr hdet
  have hG : (B * B.transpose) * (B * B.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hR : B * (B.transpose * (B * B.transpose)⁻¹) = 1 := by
    simpa only [Matrix.mul_assoc] using hG
  have hBP := mul_actual_eq_one_of_right_inverse B _ hR
  have hPG : pseudoInverse B * (B * B.transpose) = B.transpose := by
    calc
      _ = (pseudoInverse B * B) * B.transpose := by simp only [Matrix.mul_assoc]
      _ = (pseudoInverse B * B).transpose * B.transpose := by rw [pseudoinverse_mul_transpose]
      _ = B.transpose * (B * pseudoInverse B).transpose := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = B.transpose := by rw [hBP, Matrix.transpose_one, Matrix.mul_one]
  calc
    pseudoInverse B = (pseudoInverse B * (B * B.transpose)) * (B * B.transpose)⁻¹ := by
      rw [Matrix.mul_assoc, hG, Matrix.mul_one]
    _ = B.transpose * (B * B.transpose)⁻¹ := by rw [hPG]

theorem full_column_formula {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (hdet : (B.transpose * B).det ≠ 0) :
    pseudoInverse B = (B.transpose * B)⁻¹ * B.transpose := by
  have h := full_row_formula B.transpose (by simpa only [Matrix.transpose_transpose] using hdet)
  have ht := congrArg Matrix.transpose h
  simpa only [transpose, Matrix.transpose_transpose, Matrix.transpose_mul,
    Matrix.transpose_nonsing_inv] using ht

theorem orthonormal_columns {a b : ℕ} (Q : Matrix (Fin a) (Fin b) ℝ)
    (hQ : Q.transpose * Q = 1) : pseudoInverse Q = Q.transpose := by
  apply actual_eq_of_isMP
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.mul_assoc, hQ, Matrix.mul_one]
  · rw [hQ, Matrix.one_mul]
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [hQ, Matrix.transpose_one]

#assert_trust kernel full_row_formula
#assert_trust kernel full_column_formula
#assert_trust kernel orthonormal_columns
#print axioms full_column_formula
end NLA.Proofs.RE06.Pseudo
