import NLA.Proofs.RE06.RepairProjection

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

theorem full_column_pseudoinverse_mul {a b : ℕ} (S : Matrix (Fin a) (Fin b) ℝ)
    (hS : (S.transpose*S).det ≠ 0) : pseudoInverse S*S=1 := by
  rw [Pseudo.full_column_formula S hS, Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hS)

theorem regression_coefficients {n d c ell : ℕ}
    (Q : Matrix (Fin n) (Fin d) ℝ) (C : Matrix (Fin n) (Fin c) ℝ)
    (Ht : Matrix (Fin ell) (Fin n) ℝ)
    (hS : ((Ht*Q).transpose*(Ht*Q)).det ≠ 0) :
    pseudoInverse (Ht*Q)*(Ht*C) = Q.transpose*C +
      pseudoInverse (Ht*Q)*(Ht*rangeResidual Q C) := by
  have he : C = Q*(Q.transpose*C)+rangeResidual Q C := by
    unfold rangeResidual
    abel
  calc
    _ = pseudoInverse (Ht*Q)*(Ht*(Q*(Q.transpose*C)+rangeResidual Q C)) := by
      conv_lhs => rw [he]
    _ = (pseudoInverse (Ht*Q)*(Ht*Q))*(Q.transpose*C) +
        pseudoInverse (Ht*Q)*(Ht*rangeResidual Q C) := by
      simp only [Matrix.mul_add, Matrix.mul_assoc]
    _ = _ := by rw [full_column_pseudoinverse_mul (Ht*Q) hS, Matrix.one_mul]

theorem regression_error_decomposition {n d c ell : ℕ}
    (Q : Matrix (Fin n) (Fin d) ℝ) (C : Matrix (Fin n) (Fin c) ℝ)
    (Ht : Matrix (Fin ell) (Fin n) ℝ)
    (hS : ((Ht*Q).transpose*(Ht*Q)).det ≠ 0) :
    C-Q*pseudoInverse (Ht*Q)*(Ht*C) = rangeResidual Q C -
      Q*(pseudoInverse (Ht*Q)*(Ht*rangeResidual Q C)) := by
  rw [Matrix.mul_assoc, regression_coefficients Q C Ht hS, Matrix.mul_add]
  unfold rangeResidual
  abel

theorem regression_error_energy {n d c ell : ℕ}
    (Q : Matrix (Fin n) (Fin d) ℝ) (hQ : Q.transpose*Q=1)
    (C : Matrix (Fin n) (Fin c) ℝ) (Ht : Matrix (Fin ell) (Fin n) ℝ)
    (hS : ((Ht*Q).transpose*(Ht*Q)).det ≠ 0) :
    squaredFrobenius (C-Q*pseudoInverse (Ht*Q)*(Ht*C)) 0 =
      squaredFrobenius (rangeResidual Q C) 0 +
      squaredFrobenius (pseudoInverse (Ht*Q)*(Ht*rangeResidual Q C)) 0 := by
  have ht := congrArg Matrix.transpose (rangeResidual_orthogonal Q hQ C)
  have hR : (rangeResidual Q C).transpose*Q=0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using ht
  have hz : (rangeResidual Q C).transpose *
      (Q*(pseudoInverse (Ht*Q)*(Ht*rangeResidual Q C))) = 0 := by
    rw [← Matrix.mul_assoc, hR, Matrix.zero_mul]
  rw [regression_error_decomposition Q C Ht hS,
    squaredFrobenius_pythagoras _ _ hz, squaredFrobenius_left_isometry Q hQ]

/-- The fixed-width SVD repair has the same exact nonnegative error split,
including rank-zero Y. Every hypothesis is a concrete internal full-rank event. -/
theorem actual_repair_error_energy {n k d c ell : ℕ}
    (Y : Matrix (Fin n) (Fin k) ℝ) (Q : Matrix (Fin n) (Fin d) ℝ)
    (hQ : Q.transpose*Q=1) (C : Matrix (Fin n) (Fin c) ℝ)
    (Ht : Matrix (Fin ell) (Fin n) ℝ)
    (hrange : Set.range Q.mulVec=Set.range Y.mulVec)
    (hS : ((Ht*Q).transpose*(Ht*Q)).det ≠ 0) :
    squaredFrobenius (C-Y*pseudoInverse (Ht*Y)*(Ht*C)) 0 =
      squaredFrobenius (rangeResidual Q C) 0 +
      squaredFrobenius (pseudoInverse (Ht*Q)*(Ht*rangeResidual Q C)) 0 := by
  rw [Pseudo.repair_orthonormal_range Y Q Ht hQ hrange hS]
  exact regression_error_energy Q hQ C Ht hS

#assert_trust kernel full_column_pseudoinverse_mul
#assert_trust kernel regression_coefficients
#assert_trust kernel regression_error_decomposition
#assert_trust kernel regression_error_energy
#assert_trust kernel actual_repair_error_energy
#print axioms actual_repair_error_energy
end NLA.Proofs.RE06.Repair
