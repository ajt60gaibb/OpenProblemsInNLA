import NLA.Proofs.RE06.PseudoInverseFullRank

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE06.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery

/-- Reverse order holds when the first factor has full column rank and the
second has full row rank, expressed as the actual pseudoinverse equations. -/
theorem reverse_order {a r b : ℕ} (C : Matrix (Fin a) (Fin r) ℝ)
    (R : Matrix (Fin r) (Fin b) ℝ)
    (hC : pseudoInverse C * C = 1) (hR : R * pseudoInverse R = 1) :
    pseudoInverse (C * R) = pseudoInverse R * pseudoInverse C := by
  apply actual_eq_of_isMP
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ = C * (R * pseudoInverse R) * (pseudoInverse C * C) * R := by
        simp only [Matrix.mul_assoc]
      _ = C * R := by rw [hR, hC]; simp only [Matrix.mul_one]
  · calc
      _ = pseudoInverse R * (pseudoInverse C * C) * (R * pseudoInverse R) * pseudoInverse C := by
        simp only [Matrix.mul_assoc]
      _ = pseudoInverse R * pseudoInverse C := by rw [hC, hR]; simp only [Matrix.mul_one]
  · have hp : (C * R) * (pseudoInverse R * pseudoInverse C) = C * pseudoInverse C := by
      calc
        _ = C * (R * pseudoInverse R) * pseudoInverse C := by simp only [Matrix.mul_assoc]
        _ = C * pseudoInverse C := by rw [hR, Matrix.mul_one]
    rw [hp]
    exact mul_pseudoinverse_transpose C
  · have hp : (pseudoInverse R * pseudoInverse C) * (C * R) = pseudoInverse R * R := by
      calc
        _ = pseudoInverse R * (pseudoInverse C * C) * R := by simp only [Matrix.mul_assoc]
        _ = pseudoInverse R * R := by rw [hC, Matrix.mul_one]
    rw [hp]
    exact pseudoinverse_mul_transpose R

theorem reverse_order_of_gram_det {a r b : ℕ} (C : Matrix (Fin a) (Fin r) ℝ)
    (R : Matrix (Fin r) (Fin b) ℝ)
    (hC : (C.transpose * C).det ≠ 0) (hR : (R * R.transpose).det ≠ 0) :
    pseudoInverse (C * R) = pseudoInverse R * pseudoInverse C := by
  apply reverse_order
  · rw [full_column_formula C hC, Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hC)
  · rw [full_row_formula R hR, ← Matrix.mul_assoc]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hR)

/-- Deterministic bridge from the actual fixed-width repair to a range basis.
The hypotheses are the exact rank equations to be proved on the Gaussian good
event; no hypothesis is added to any public RE-06 export. -/
theorem repair_range_factorization {n k r ell : ℕ}
    (Y : Matrix (Fin n) (Fin k) ℝ) (Q : Matrix (Fin n) (Fin r) ℝ)
    (R : Matrix (Fin r) (Fin k) ℝ) (Ht : Matrix (Fin ell) (Fin n) ℝ)
    (hY : Y = Q * R)
    (hC : pseudoInverse (Ht * Q) * (Ht * Q) = 1)
    (hR : R * pseudoInverse R = 1) :
    Y * pseudoInverse (Ht * Y) = Q * pseudoInverse (Ht * Q) := by
  rw [hY, ← Matrix.mul_assoc Ht Q R, reverse_order (Ht * Q) R hC hR]
  calc
    _ = Q * (R * pseudoInverse R) * pseudoInverse (Ht * Q) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hR, Matrix.mul_one]

theorem repair_range_factorization_of_gram_det {n k r ell : ℕ}
    (Y : Matrix (Fin n) (Fin k) ℝ) (Q : Matrix (Fin n) (Fin r) ℝ)
    (R : Matrix (Fin r) (Fin k) ℝ) (Ht : Matrix (Fin ell) (Fin n) ℝ)
    (hY : Y = Q * R)
    (hC : ((Ht * Q).transpose * (Ht * Q)).det ≠ 0)
    (hR : (R * R.transpose).det ≠ 0) :
    Y * pseudoInverse (Ht * Y) = Q * pseudoInverse (Ht * Q) := by
  apply repair_range_factorization Y Q R Ht hY
  · rw [full_column_formula (Ht * Q) hC, Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hC)
  · rw [full_row_formula R hR, ← Matrix.mul_assoc]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hR)

#assert_trust kernel reverse_order
#assert_trust kernel reverse_order_of_gram_det
#assert_trust kernel repair_range_factorization
#assert_trust kernel repair_range_factorization_of_gram_det
#print axioms repair_range_factorization
end NLA.Proofs.RE06.Pseudo
