import ProofProject.OperatorBalancedFactors
import ProofProject.BalancedSeparation
import ProofProject.SeparatedFactorSum
import ProofProject.SharpTailGeometry

/-!
# Exact-exponent synthesis for commuting separated operator pieces

All geometry and factorization inputs are discharged. What remains explicit
is the source's square-root error budget for actual commuting separators.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {n : ℕ}

/-- Actual bounded pieces and their commuting separators give the sharp
power of the number of pieces. The error shrinks as `1/n`, so the exponent
is exactly `growthExponent M`. -/
theorem separated_operator_sum_norm_le {M ε D : ℝ}
    (hM : 1 < M) (hn : 1 ≤ n) (hε0 : 0 < ε) (hε : ε ≤ 1 / (n : ℝ))
    (B : Fin n → H →L[ℂ] H) (hB : ∀ j, ‖B j‖ ≤ D)
    (hsep : ∀ k : ℕ, 0 < k → k < n → ∃ R : H →L[ℂ] H,
      ‖R‖ ≤ M ∧ (∀ j, Commute R (B j)) ∧
      Real.sqrt (M + 1) * sqrtSeparationError B R k ≤ ε) :
    ‖∑ j, B j‖ ≤
      ((16 * Real.exp 2) * (M + 1) ^ 2 * Real.exp (growthExponentLipschitzConstant M)) *
        (D + 1) * (n : ℝ) ^ growthExponent M := by
  have hD : 0 ≤ D := (norm_nonneg (B ⟨0, by omega⟩)).trans (hB _)
  let X := fun j => operatorLeftFactor (B j)
  let Y := fun j => operatorRightFactor (B j)
  have hX : ∀ j, star (X j) * X j = CFC.abs (B j) := fun j => operatorLeftFactor_gram (B j)
  have hY : ∀ j, Y j * star (Y j) = CFC.abs (star (B j)) := fun j => operatorRightFactor_gram (B j)
  obtain ⟨hsepX, hsepY⟩ := balancedFactors_hasApproximateSeparators B X Y hX hY hsep
  have hNX : ∀ j, ‖(X j).adjoint‖ ≤ Real.sqrt D := by
    intro j
    change ‖star (operatorLeftFactor (B j))‖ ≤ Real.sqrt D
    rw [norm_star, norm_operatorLeftFactor]
    exact Real.sqrt_le_sqrt (hB j)
  have hNY : ∀ j, ‖Y j‖ ≤ Real.sqrt D := by
    intro j
    change ‖operatorRightFactor (B j)‖ ≤ Real.sqrt D
    rw [norm_operatorRightFactor]
    exact Real.sqrt_le_sqrt (hB j)
  have h := separated_factor_sum_norm_le sharp_tail_geometry hM hn hε0 hε X Y hNX hNY hsepX hsepY
  have hprod (j : Fin n) : (Y j).comp (X j) = B j := operatorFactors_mul (B j)
  simpa only [hprod, Real.sq_sqrt hD] using h

/-- A retained subfamily may have fewer than the original `N` pieces. Using
error `1/N` controls its sum by `N^α`, including an empty retained family. -/
theorem separated_operator_sum_norm_le_of_length_le {M D : ℝ} {N : ℕ}
    (hM : 1 < M) (hD : 0 ≤ D) (hN : 1 ≤ N) (hnN : n ≤ N)
    (B : Fin n → H →L[ℂ] H) (hB : ∀ j, ‖B j‖ ≤ D)
    (hsep : ∀ k : ℕ, 0 < k → k < n → ∃ R : H →L[ℂ] H,
      ‖R‖ ≤ M ∧ (∀ j, Commute R (B j)) ∧
      Real.sqrt (M + 1) * sqrtSeparationError B R k ≤ 1 / (N : ℝ)) :
    ‖∑ j, B j‖ ≤
      ((16 * Real.exp 2) * (M + 1) ^ 2 * Real.exp (growthExponentLipschitzConstant M)) *
        (D + 1) * (N : ℝ) ^ growthExponent M := by
  by_cases hn : n = 0
  · subst n
    simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    positivity
  · have hn' : 1 ≤ n := by omega
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_ne_zero hn)
    have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have h := separated_operator_sum_norm_le hM hn' (one_div_pos.mpr hNR)
      (one_div_le_one_div_of_le hnR (by exact_mod_cast hnN)) B hB hsep
    apply h.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnN) (growthExponent_nonneg M))
      (by positivity)

end ProofProject
