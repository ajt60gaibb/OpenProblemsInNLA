import NLA.Proofs.RE06.PseudoInverseProduct

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE06.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery

theorem range_subset_iff_matrix_factor {n a b : ℕ}
    (A : Matrix (Fin n) (Fin a) ℝ) (B : Matrix (Fin n) (Fin b) ℝ) :
    Set.range A.mulVec ⊆ Set.range B.mulVec ↔
      ∃ R : Matrix (Fin b) (Fin a) ℝ, A = B * R := by
  constructor
  · intro h
    have hc : ∀ j : Fin a, ∃ v : Fin b → ℝ, B.mulVec v = fun i => A i j := by
      intro j
      apply h
      exact ⟨Pi.single j 1, Matrix.mulVec_single_one A j⟩
    choose v hv using hc
    refine ⟨fun i j => v j i, ?_⟩
    ext i j
    simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply] using (congrFun (hv j) i).symm
  · rintro ⟨R, rfl⟩ _ ⟨v, rfl⟩
    exact ⟨R.mulVec v, (Matrix.mulVec_mulVec _ _ _).symm⟩

/-- The source's orthonormal range-basis repair equals the frozen fixed-width
SVD repair on the exact full-column-rank event for `Ht*Q`. No rank restriction
on `Y` is needed; the basis may have dimension zero. -/
theorem repair_orthonormal_range {n k r ell : ℕ}
    (Y : Matrix (Fin n) (Fin k) ℝ) (Q : Matrix (Fin n) (Fin r) ℝ)
    (Ht : Matrix (Fin ell) (Fin n) ℝ)
    (hQ : Q.transpose * Q = 1)
    (hrange : Set.range Q.mulVec = Set.range Y.mulVec)
    (hC : ((Ht * Q).transpose * (Ht * Q)).det ≠ 0) :
    Y * pseudoInverse (Ht * Y) = Q * pseudoInverse (Ht * Q) := by
  obtain ⟨R, hY⟩ := (range_subset_iff_matrix_factor Y Q).mp hrange.symm.subset
  obtain ⟨S, hS⟩ := (range_subset_iff_matrix_factor Q Y).mp hrange.subset
  have hRS : R * S = 1 := by
    calc
      R * S = (Q.transpose * Q) * (R * S) := by rw [hQ, Matrix.one_mul]
      _ = Q.transpose * (Q * R) * S := by simp only [Matrix.mul_assoc]
      _ = Q.transpose * Y * S := by rw [← hY]
      _ = Q.transpose * Q := by rw [Matrix.mul_assoc, ← hS]
      _ = 1 := hQ
  apply repair_range_factorization Y Q R Ht hY
  · rw [full_column_formula (Ht * Q) hC, Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hC)
  · exact mul_actual_eq_one_of_right_inverse R S hRS

#assert_trust kernel range_subset_iff_matrix_factor
#assert_trust kernel repair_orthonormal_range
#print axioms repair_orthonormal_range
end NLA.Proofs.RE06.Pseudo
