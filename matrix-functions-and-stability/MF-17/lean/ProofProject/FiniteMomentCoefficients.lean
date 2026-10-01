import ProofProject.FiniteMomentOrthogonality

/-! Shifted finite coefficient extraction from the exact source moments. -/

noncomputable section

open MeasureTheory

namespace ProofProject

lemma sourceCircle_pow_mul_conj_pow_of_le (θ : ℝ) {i j : ℕ} (hji : j ≤ i) :
    sourceCircle θ ^ j * starRingEnd ℂ (sourceCircle θ ^ i) =
      starRingEnd ℂ (sourceCircle θ ^ (i - j)) := by
  rw [← sourceCircle_pow_mul_conj_pow θ hji, map_mul, starRingEnd_self_apply]
  ring

lemma sourcePolynomial_upper_coefficient_expansion {n : ℕ}
    (F : ℂ → ℂ) (a : Fin n → ℂ) (i : Fin n)
    (ha : ∀ j, a j ≠ 0 → i.val ≤ j.val) (θ : ℝ) :
    F (sourceCircle θ) * sourcePolynomial a θ *
        starRingEnd ℂ (sourceCircle θ ^ i.val) =
      ∑ j, a j * (F (sourceCircle θ) * sourceCircle θ ^ (j.val - i.val)) := by
  simp only [sourcePolynomial, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases haj : a j = 0
  · simp [haj]
  calc
    _ = a j * (F (sourceCircle θ) *
        (sourceCircle θ ^ j.val * starRingEnd ℂ (sourceCircle θ ^ i.val))) := by ring
    _ = _ := by rw [sourceCircle_pow_mul_conj_pow θ (ha j haj)]

lemma sourcePolynomial_lower_coefficient_expansion {n : ℕ}
    (F : ℂ → ℂ) (b : Fin n → ℂ) (i : Fin n)
    (hb : ∀ j, b j ≠ 0 → j.val ≤ i.val) (θ : ℝ) :
    starRingEnd ℂ (F (sourceCircle θ)) * sourcePolynomial b θ *
        starRingEnd ℂ (sourceCircle θ ^ i.val) =
      ∑ j, b j * starRingEnd ℂ
        (F (sourceCircle θ) * sourceCircle θ ^ (i.val - j.val)) := by
  simp only [sourcePolynomial, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hbj : b j = 0
  · simp [hbj]
  calc
    _ = b j * (starRingEnd ℂ (F (sourceCircle θ)) *
        (sourceCircle θ ^ j.val * starRingEnd ℂ (sourceCircle θ ^ i.val))) := by ring
    _ = _ := by rw [sourceCircle_pow_mul_conj_pow_of_le θ (hb j hbj), map_mul]

lemma sourceWeightFactor_conj_moment_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    IntegrableOn (fun θ => starRingEnd ℂ
      (sourceWeightFactor α (sourceCircle θ) * sourceCircle θ ^ k))
      (Set.Icc (-Real.pi) Real.pi) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp
    (sourceWeightFactor_moment_integrable hα0 hα1 k)

/-- The upper part of the shifted coefficient formula is integrable. -/
theorem sourceWeightFactor_upper_coefficient_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (a : Fin n → ℂ) (i : Fin n)
    (ha : ∀ j, a j ≠ 0 → i.val ≤ j.val) :
    IntegrableOn (fun θ => sourceWeightFactor α (sourceCircle θ) *
      sourcePolynomial a θ * starRingEnd ℂ (sourceCircle θ ^ i.val))
      (Set.Icc (-Real.pi) Real.pi) := by
  simp_rw [sourcePolynomial_upper_coefficient_expansion (sourceWeightFactor α) a i ha]
  exact integrable_finsetSum _ fun j _ =>
    (sourceWeightFactor_moment_integrable hα0 hα1 (j.val - i.val)).const_mul _

/-- The conjugated lower part of the shifted coefficient formula is integrable. -/
theorem sourceWeightFactor_lower_coefficient_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (b : Fin n → ℂ) (i : Fin n)
    (hb : ∀ j, b j ≠ 0 → j.val ≤ i.val) :
    IntegrableOn (fun θ => starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) *
      sourcePolynomial b θ * starRingEnd ℂ (sourceCircle θ ^ i.val))
      (Set.Icc (-Real.pi) Real.pi) := by
  simp_rw [sourcePolynomial_lower_coefficient_expansion (sourceWeightFactor α) b i hb]
  exact integrable_finsetSum _ fun j _ =>
    (sourceWeightFactor_conj_moment_integrable hα0 hα1 (i.val - j.val)).const_mul _

/-- Extracting the boundary coefficient of an upper frequency block. -/
theorem sourceWeightFactor_upper_coefficient_integral {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (a : Fin n → ℂ) (i : Fin n)
    (ha : ∀ j, a j ≠ 0 → i.val ≤ j.val) :
    (∫ θ in Set.Icc (-Real.pi) Real.pi,
      sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ *
        starRingEnd ℂ (sourceCircle θ ^ i.val)) = (2 * Real.pi : ℂ) * a i := by
  simp_rw [sourcePolynomial_upper_coefficient_expansion (sourceWeightFactor α) a i ha]
  rw [integral_finsetSum _ (fun j _ =>
    (sourceWeightFactor_moment_integrable hα0 hα1 (j.val - i.val)).const_mul _)]
  simp_rw [integral_const_mul]
  change (∑ j, a j * sourceAngularMoment (sourceWeightFactor α) (j.val - i.val)) = _
  rw [Fintype.sum_eq_single i]
  · simp [sourceAngularMoment_sourceWeightFactor hα0 hα1, mul_comm]
  · intro j hji
    by_cases haj : a j = 0
    · simp [haj]
    have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hpos : 0 < j.val - i.val := by have := ha j haj; omega
    rw [sourceAngularMoment_sourceWeightFactor hα0 hα1, if_neg (Nat.ne_of_gt hpos), mul_zero]

/-- Extracting the boundary coefficient of a conjugated lower frequency block.
The coefficient itself remains unconjugated. -/
theorem sourceWeightFactor_lower_coefficient_integral {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (b : Fin n → ℂ) (i : Fin n)
    (hb : ∀ j, b j ≠ 0 → j.val ≤ i.val) :
    (∫ θ in Set.Icc (-Real.pi) Real.pi,
      starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) * sourcePolynomial b θ *
        starRingEnd ℂ (sourceCircle θ ^ i.val)) = (2 * Real.pi : ℂ) * b i := by
  simp_rw [sourcePolynomial_lower_coefficient_expansion (sourceWeightFactor α) b i hb]
  rw [integral_finsetSum _ (fun j _ =>
    (sourceWeightFactor_conj_moment_integrable hα0 hα1 (i.val - j.val)).const_mul _)]
  simp_rw [integral_const_mul, integral_conj]
  change (∑ j, b j * starRingEnd ℂ
    (sourceAngularMoment (sourceWeightFactor α) (i.val - j.val))) = _
  rw [Fintype.sum_eq_single i]
  · simp [sourceAngularMoment_sourceWeightFactor hα0 hα1, mul_comm]
    exact Or.inl (Complex.conj_ofReal 2)
  · intro j hji
    by_cases hbj : b j = 0
    · simp [hbj]
    have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hpos : 0 < i.val - j.val := by have := hb j hbj; omega
    simp only [sourceAngularMoment_sourceWeightFactor hα0 hα1,
      if_neg (Nat.ne_of_gt hpos), map_zero, mul_zero]

/-- The two overlapping boundary coefficients are integrable together. -/
theorem sourceWeightFactor_shifted_coefficient_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ}
    (a b : Fin n → ℂ) (i : Fin n)
    (ha : ∀ j, a j ≠ 0 → i.val ≤ j.val)
    (hb : ∀ j, b j ≠ 0 → j.val ≤ i.val) :
    IntegrableOn (fun θ =>
      (sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ +
        starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) * sourcePolynomial b θ) *
          starRingEnd ℂ (sourceCircle θ ^ i.val))
      (Set.Icc (-Real.pi) Real.pi) := by
  simp_rw [add_mul]
  exact (sourceWeightFactor_upper_coefficient_integrable hα0 hα1 a i ha).add
    (sourceWeightFactor_lower_coefficient_integrable hα0 hα1 b i hb)

/-- The exact shifted coefficient identity used by the source's boundary
estimate. Upper and lower supports may both include the index `i`. -/
theorem sourceWeightFactor_shifted_coefficient_integral {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ}
    (a b : Fin n → ℂ) (i : Fin n)
    (ha : ∀ j, a j ≠ 0 → i.val ≤ j.val)
    (hb : ∀ j, b j ≠ 0 → j.val ≤ i.val) :
    (∫ θ in Set.Icc (-Real.pi) Real.pi,
      (sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ +
        starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) * sourcePolynomial b θ) *
          starRingEnd ℂ (sourceCircle θ ^ i.val)) = (2 * Real.pi : ℂ) * (a i + b i) := by
  simp_rw [add_mul]
  rw [integral_add (sourceWeightFactor_upper_coefficient_integrable hα0 hα1 a i ha)
    (sourceWeightFactor_lower_coefficient_integrable hα0 hα1 b i hb),
    sourceWeightFactor_upper_coefficient_integral hα0 hα1 a i ha,
    sourceWeightFactor_lower_coefficient_integral hα0 hα1 b i hb, mul_add]

end ProofProject
