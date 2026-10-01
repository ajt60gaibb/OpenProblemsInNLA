import ProofProject.SourceBoundaryMoments

/-! Finite polynomial orthogonality from vanishing positive angular moments. -/

noncomputable section

open MeasureTheory

namespace ProofProject

/-- A finite analytic polynomial evaluated on the source circle. -/
def sourcePolynomial {n : ℕ} (a : Fin n → ℂ) (θ : ℝ) : ℂ :=
  ∑ i, a i * sourceCircle θ ^ i.val

/-- Cancellation of two nonnegative circle frequencies uses only unit modulus. -/
lemma sourceCircle_pow_mul_conj_pow (θ : ℝ) {i j : ℕ} (hji : j ≤ i) :
    sourceCircle θ ^ i * starRingEnd ℂ (sourceCircle θ ^ j) =
      sourceCircle θ ^ (i - j) := by
  rw [← Complex.inv_eq_conj (by simp [norm_pow]),
    ← pow_sub₀ _ (by exact Complex.exp_ne_zero _) hji]

/-- Disjoint lower and upper supports turn every surviving cross term into a
positive frequency. The formula also covers zero coefficients and empty families. -/
lemma sourcePolynomial_cross_expansion {n m cut : ℕ}
    (a : Fin n → ℂ) (b : Fin m → ℂ)
    (ha : ∀ i, a i ≠ 0 → cut ≤ i.val)
    (hb : ∀ j, b j ≠ 0 → j.val < cut) (F : ℂ → ℂ) (θ : ℝ) :
    F (sourceCircle θ) * sourcePolynomial a θ *
        starRingEnd ℂ (sourcePolynomial b θ) =
      ∑ i, ∑ j, (a i * starRingEnd ℂ (b j)) *
        (F (sourceCircle θ) * sourceCircle θ ^ (i.val - j.val)) := by
  simp only [sourcePolynomial, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hai : a i = 0
  · simp [hai]
  by_cases hbj : b j = 0
  · simp [hbj]
  have hji : j.val ≤ i.val := (hb j hbj).le.trans (ha i hai)
  calc
    _ = (a i * starRingEnd ℂ (b j)) * (F (sourceCircle θ) *
        (sourceCircle θ ^ i.val * starRingEnd ℂ (sourceCircle θ ^ j.val))) := by ring
    _ = _ := by rw [sourceCircle_pow_mul_conj_pow θ hji]

/-- Integrability of a separated-frequency polynomial cross term follows from
integrability of the nonnegative moments alone. -/
theorem sourcePolynomial_cross_integrable {F : ℂ → ℂ}
    (hF : ∀ k : ℕ, IntegrableOn
      (fun θ => F (sourceCircle θ) * sourceCircle θ ^ k)
      (Set.Icc (-Real.pi) Real.pi))
    {n m cut : ℕ} (a : Fin n → ℂ) (b : Fin m → ℂ)
    (ha : ∀ i, a i ≠ 0 → cut ≤ i.val)
    (hb : ∀ j, b j ≠ 0 → j.val < cut) :
    IntegrableOn (fun θ => F (sourceCircle θ) * sourcePolynomial a θ *
      starRingEnd ℂ (sourcePolynomial b θ)) (Set.Icc (-Real.pi) Real.pi) := by
  simp_rw [sourcePolynomial_cross_expansion a b ha hb F]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hF (i.val - j.val)).const_mul _

/-- Upper and lower finite frequency blocks are orthogonal against any factor
whose positive angular moments vanish. -/
theorem sourcePolynomial_cross_integral_eq_zero {F : ℂ → ℂ}
    (hF : ∀ k : ℕ, IntegrableOn
      (fun θ => F (sourceCircle θ) * sourceCircle θ ^ k)
      (Set.Icc (-Real.pi) Real.pi))
    (hmoment : ∀ k : ℕ, 0 < k → sourceAngularMoment F k = 0)
    {n m cut : ℕ} (a : Fin n → ℂ) (b : Fin m → ℂ)
    (ha : ∀ i, a i ≠ 0 → cut ≤ i.val)
    (hb : ∀ j, b j ≠ 0 → j.val < cut) :
    (∫ θ in Set.Icc (-Real.pi) Real.pi,
      F (sourceCircle θ) * sourcePolynomial a θ *
        starRingEnd ℂ (sourcePolynomial b θ)) = 0 := by
  simp_rw [sourcePolynomial_cross_expansion a b ha hb F]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    (hF (i.val - j.val)).const_mul _)]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_finsetSum _ (fun j _ => (hF (i.val - j.val)).const_mul _)]
  apply Finset.sum_eq_zero
  intro j hj
  rw [integral_const_mul]
  by_cases hai : a i = 0
  · simp [hai]
  by_cases hbj : b j = 0
  · simp [hbj]
  change (a i * starRingEnd ℂ (b j)) * sourceAngularMoment F (i.val - j.val) = 0
  rw [hmoment _ (Nat.sub_pos_of_lt ((hb j hbj).trans_le (ha i hai))), mul_zero]

/-- Orthogonality for the actual square of the source factor, with no remaining
moment hypothesis. -/
theorem sourceWeightFactor_sq_polynomial_orthogonality {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    {n m cut : ℕ} (a : Fin n → ℂ) (b : Fin m → ℂ)
    (ha : ∀ i, a i ≠ 0 → cut ≤ i.val)
    (hb : ∀ j, b j ≠ 0 → j.val < cut) :
    (∫ θ in Set.Icc (-Real.pi) Real.pi,
      sourceWeightFactor α (sourceCircle θ) ^ 2 * sourcePolynomial a θ *
        starRingEnd ℂ (sourcePolynomial b θ)) = 0 := by
  apply sourcePolynomial_cross_integral_eq_zero (F := fun z => sourceWeightFactor α z ^ 2)
    (sourceWeightFactor_sq_moment_integrable hα0 hα1) _ a b ha hb
  intro k hk
  simpa only [if_neg (Nat.ne_of_gt hk)] using
    sourceAngularMoment_sourceWeightFactor_sq hα0 hα1 k

/-- The orthogonality integrand for the actual source factor is integrable. -/
theorem sourceWeightFactor_sq_polynomial_cross_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    {n m cut : ℕ} (a : Fin n → ℂ) (b : Fin m → ℂ)
    (ha : ∀ i, a i ≠ 0 → cut ≤ i.val)
    (hb : ∀ j, b j ≠ 0 → j.val < cut) :
    IntegrableOn (fun θ => sourceWeightFactor α (sourceCircle θ) ^ 2 *
      sourcePolynomial a θ * starRingEnd ℂ (sourcePolynomial b θ))
      (Set.Icc (-Real.pi) Real.pi) :=
  sourcePolynomial_cross_integrable (F := fun z => sourceWeightFactor α z ^ 2)
    (sourceWeightFactor_sq_moment_integrable hα0 hα1)
    a b ha hb

end ProofProject
