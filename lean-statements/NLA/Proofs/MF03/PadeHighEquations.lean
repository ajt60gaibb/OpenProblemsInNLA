import NLA.Proofs.MF03.PadeNumeratorPolynomial
import NLA.Proofs.MF03.CosineCoefficientTransfer
import NLA.Statements.MF03

/-! The original Toeplitz system implies every high-degree equation of the
frozen all-order normalized MF-03 Padé specification. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.MF03

private theorem cosinePade_high_row_complex (m : ℕ) (r : Fin m) :
    (∑ c : Fin m,
      (cosinePadeNonconstantCoeff m c : ℂ) *
        (cosineElementaryCoeff (m + r.val - c.val) : ℂ)) =
      -(cosineElementaryCoeff (m + r.val + 1) : ℂ) := by
  have hrow := congrFun (cosinePadeNonconstantCoeff_system m) r
  simp only [Matrix.mulVec, dotProduct, cosinePadeToeplitz,
    cosinePadeRHS] at hrow
  have hrowC := congrArg (fun x : ℝ => (x : ℂ)) hrow
  push_cast at hrowC
  simpa only [mul_comm] using hrowC

private theorem cosinePade_high_elementary_equation (m : ℕ) (r : Fin m) :
    (∑ i ∈ Finset.range (m + r.val + 2),
      (cosinePadeDenominator m).coeff i *
        (cosineElementaryCoeff (m + r.val + 1 - i) : ℂ)) = 0 := by
  let n := m + r.val + 1
  let f : ℕ → ℂ := fun i =>
    (cosinePadeDenominator m).coeff i *
      (cosineElementaryCoeff (n - i) : ℂ)
  change (∑ i ∈ Finset.range (n + 1), f i) = 0
  have hn : n + 1 = (m + 1) + (r.val + 1) := by
    dsimp [n]
    omega
  rw [hn, Finset.sum_range_add]
  have htail :
      (∑ i ∈ Finset.range (r.val + 1), f (m + 1 + i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hmi : m < m + 1 + i := by omega
    simp [f, cosinePadeDenominator_coeff_above m (m + 1 + i) hmi]
  rw [htail, add_zero, Finset.sum_range_succ']
  have hfirst : f 0 = (cosineElementaryCoeff n : ℂ) := by
    simp [f, cosinePadeDenominator_coeff_zero]
  rw [hfirst]
  have hrest : (∑ i ∈ Finset.range m, f (i + 1)) =
      -(cosineElementaryCoeff n : ℂ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    convert cosinePade_high_row_complex m r using 1
    · congr 1
      funext c
      simp only [f, cosinePadeDenominator_coeff_fin]
      congr 1
      dsimp [n]
      have hc := c.isLt
      have hindex : m + r.val + 1 - (c.val + 1) =
          m + r.val - c.val := by omega
      rw [hindex]
  rw [hrest]
  simp

private theorem cosinePade_factorial_as_elementary (k : ℕ) :
    (cosineElementaryCoeff k : ℂ) =
      (1 : ℂ) / ((2 * k).factorial : ℂ) := by
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (cosineElementaryCoeff_eq_factorial k)
  push_cast at h
  exact h

private theorem cosinePade_high_factorial_equation (m : ℕ) (r : Fin m) :
    (∑ i ∈ Finset.range (m + r.val + 2),
      (cosinePadeDenominator m).coeff i /
        ((2 * (m + r.val + 1 - i)).factorial : ℂ)) = 0 := by
  rw [← cosinePade_high_elementary_equation m r]
  apply Finset.sum_congr rfl
  intro i _
  rw [cosinePade_factorial_as_elementary]
  ring

/-- The literal all-order Padé numerator and denominator satisfy every
coefficient condition of the frozen normalized MF-03 specification. -/
theorem cosinePade_normalized (m : ℕ) :
    NLA.Statements.MF03.NormalizedPadeRepresentation m
      (cosinePadeNumerator m) (cosinePadeDenominator m) := by
  refine ⟨cosinePadeNumerator_natDegree_le m,
    cosinePadeDenominator_natDegree_le m, ?_, ?_⟩
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using
      cosinePadeDenominator_coeff_zero m
  · intro j hj
    by_cases hlow : j ≤ m
    · exact (cosinePadeNumerator_coeff_le m j hlow).symm
    · let r : Fin m := ⟨j - (m + 1), by omega⟩
      have hr : m + r.val + 1 = j := by
        dsimp [r]
        omega
      rw [cosinePadeNumerator_coeff_above m j (by omega)]
      rw [← hr]
      exact cosinePade_high_factorial_equation m r

#assert_trust kernel cosinePade_high_row_complex
#assert_trust kernel cosinePade_high_elementary_equation
#assert_trust kernel cosinePade_normalized
#print axioms cosinePade_normalized

end NLA.Proofs.MF03
