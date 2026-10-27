import NLA.Proofs.RE06.PseudoInverseIdentities

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE06.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery

theorem symmetric_absorption_unique {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.transpose = P) (hQ : Q.transpose = Q)
    (hPQ : P * Q = Q) (hQP : Q * P = P) : P = Q := by
  have ht : Q * P = Q := by
    simpa only [Matrix.transpose_mul, hP, hQ] using congrArg Matrix.transpose hPQ
  exact hQP.symm.trans ht

theorem isMP_unique {a b : ℕ} {B : Matrix (Fin a) (Fin b) ℝ}
    {X Y : Matrix (Fin b) (Fin a) ℝ} (hX : IsMP B X) (hY : IsMP B Y) : X = Y := by
  have hcols : B * X = B * Y := by
    apply symmetric_absorption_unique _ _ hX.2.2.1 hY.2.2.1
    · calc
        (B * X) * (B * Y) = (B * X * B) * Y := by simp only [Matrix.mul_assoc]
        _ = B * Y := by rw [hX.1]
    · calc
        (B * Y) * (B * X) = (B * Y * B) * X := by simp only [Matrix.mul_assoc]
        _ = B * X := by rw [hY.1]
  have hrows : Y * B = X * B := by
    have hYX : (Y * B) * (X * B) = Y * B := by
      calc
        (Y * B) * (X * B) = Y * (B * X * B) := by simp only [Matrix.mul_assoc]
        _ = Y * B := by rw [hX.1]
    have hXY : (X * B) * (Y * B) = X * B := by
      calc
        (X * B) * (Y * B) = X * (B * Y * B) := by simp only [Matrix.mul_assoc]
        _ = X * B := by rw [hY.1]
    have ht : (X * B) * (Y * B) = Y * B := by
      simpa only [Matrix.transpose_mul, hX.2.2.2, hY.2.2.2] using
        congrArg Matrix.transpose hYX
    exact ht.symm.trans hXY
  calc
    X = X * B * X := hX.2.1.symm
    _ = X * B * Y := by simpa only [Matrix.mul_assoc] using congrArg (X * ·) hcols
    _ = Y * B * Y := by rw [hrows]
    _ = Y := hY.2.1

theorem actual_eq_of_isMP {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (P : Matrix (Fin b) (Fin a) ℝ) (hP : IsMP B P) : pseudoInverse B = P :=
  isMP_unique (actual_isMP B) hP

theorem zero {a b : ℕ} : pseudoInverse (0 : Matrix (Fin a) (Fin b) ℝ) = 0 := by
  apply actual_eq_of_isMP
  simp [IsMP]

theorem transpose {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    pseudoInverse B.transpose = (pseudoInverse B).transpose := by
  apply actual_eq_of_isMP
  have h := actual_isMP B
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose h.1
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose h.2.1
  · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h.2.2.2.symm
  · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h.2.2.1.symm

#assert_trust kernel isMP_unique
#assert_trust kernel actual_eq_of_isMP
#assert_trust kernel zero
#assert_trust kernel transpose
#print axioms transpose
end NLA.Proofs.RE06.Pseudo
