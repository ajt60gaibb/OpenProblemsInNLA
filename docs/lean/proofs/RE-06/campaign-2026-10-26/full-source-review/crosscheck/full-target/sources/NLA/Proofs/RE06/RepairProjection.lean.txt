import NLA.Proofs.RE06.GaussianOrthogonal
import NLA.Proofs.RE06.Frobenius
import NLA.Proofs.RE06.PseudoInverseRange

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

theorem squaredFrobenius_zero_nonneg {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) :
    0 ≤ squaredFrobenius X 0 := by
  unfold squaredFrobenius
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem squaredFrobenius_sub_zero {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) ℝ) :
    squaredFrobenius (X-Y) 0 = squaredFrobenius X Y := by
  simp [squaredFrobenius]

theorem squaredFrobenius_pythagoras {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) ℝ)
    (h : X.transpose * Y = 0) :
    squaredFrobenius (X-Y) 0 = squaredFrobenius X 0 + squaredFrobenius Y 0 := by
  have h' : Y.transpose * X = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using
      congrArg Matrix.transpose h
  simp only [squaredFrobenius_zero_eq_trace, Matrix.transpose_sub, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.trace_sub, h, h', Matrix.trace_zero]
  ring

def rangeResidual {n d c : ℕ} (Q : Matrix (Fin n) (Fin d) ℝ)
    (C : Matrix (Fin n) (Fin c) ℝ) : Matrix (Fin n) (Fin c) ℝ :=
  C-Q*(Q.transpose*C)

theorem rangeResidual_orthogonal {n d c : ℕ} (Q : Matrix (Fin n) (Fin d) ℝ)
    (hQ : Q.transpose*Q=1) (C : Matrix (Fin n) (Fin c) ℝ) :
    Q.transpose * rangeResidual Q C = 0 := by
  unfold rangeResidual
  rw [Matrix.mul_sub, ← Matrix.mul_assoc Q.transpose Q (Q.transpose*C), hQ,
    Matrix.one_mul, sub_self]

theorem rangeResidual_pythagoras {n d c : ℕ} (Q : Matrix (Fin n) (Fin d) ℝ)
    (hQ : Q.transpose*Q=1) (C : Matrix (Fin n) (Fin c) ℝ)
    (X : Matrix (Fin d) (Fin c) ℝ) :
    squaredFrobenius (C-Q*X) 0 = squaredFrobenius (rangeResidual Q C) 0 +
      squaredFrobenius (Q.transpose*C-X) 0 := by
  have hr : C-Q*X = rangeResidual Q C - Q*(X-Q.transpose*C) := by
    simp only [rangeResidual, Matrix.mul_sub]
    abel
  have hz : (rangeResidual Q C).transpose * (Q*(X-Q.transpose*C)) = 0 := by
    have ht := congrArg Matrix.transpose (rangeResidual_orthogonal Q hQ C)
    have hR : (rangeResidual Q C).transpose * Q = 0 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using ht
    rw [← Matrix.mul_assoc, hR, Matrix.zero_mul]
  rw [hr, squaredFrobenius_pythagoras _ _ hz,
    squaredFrobenius_left_isometry Q hQ]
  congr 1
  simp only [squaredFrobenius, Matrix.zero_apply, sub_zero, Matrix.sub_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rangeResidual_minimizes {n d c : ℕ} (Q : Matrix (Fin n) (Fin d) ℝ)
    (hQ : Q.transpose*Q=1) (C : Matrix (Fin n) (Fin c) ℝ)
    (X : Matrix (Fin d) (Fin c) ℝ) :
    squaredFrobenius (rangeResidual Q C) 0 ≤ squaredFrobenius (C-Q*X) 0 := by
  rw [rangeResidual_pythagoras Q hQ C X]
  exact le_add_of_nonneg_right (squaredFrobenius_zero_nonneg _)

theorem rangeResidual_le_range_approximation {n d c : ℕ}
    (Q : Matrix (Fin n) (Fin d) ℝ) (hQ : Q.transpose*Q=1)
    (C D : Matrix (Fin n) (Fin c) ℝ)
    (hD : Set.range D.mulVec ⊆ Set.range Q.mulVec) :
    squaredFrobenius (rangeResidual Q C) 0 ≤ squaredFrobenius (C-D) 0 := by
  obtain ⟨X, rfl⟩ := (Pseudo.range_subset_iff_matrix_factor D Q).mp hD
  exact rangeResidual_minimizes Q hQ C X

#assert_trust kernel squaredFrobenius_zero_nonneg
#assert_trust kernel squaredFrobenius_sub_zero
#assert_trust kernel squaredFrobenius_pythagoras
#assert_trust kernel rangeResidual_orthogonal
#assert_trust kernel rangeResidual_pythagoras
#assert_trust kernel rangeResidual_minimizes
#assert_trust kernel rangeResidual_le_range_approximation
#print axioms rangeResidual_le_range_approximation
end NLA.Proofs.RE06.Repair
