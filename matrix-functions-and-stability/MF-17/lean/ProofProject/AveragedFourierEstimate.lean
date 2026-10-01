import ProofProject.AveragedFourierOperator

/-!
# The norm estimate from finite Fourier reconstruction

The two actual averaging operators have an integrable product of norms, with
bound `M² ‖x‖ ‖y‖`. A finite scalar reconstruction with frequency budget `C`
therefore gives the source operator bound `M³ C`. Reconstruction itself is
kept explicit in this lemma and is proved separately from scalar inversion.
-/

noncomputable section

open MeasureTheory Set FourierTransform

namespace ProofProject.BoundedSemigroup

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem averagedFourierOperator_continuous (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (x : H) :
    Continuous (fun ξ => S.averagedFourierOperator N hN ξ x) := by
  simp only [averagedFourierOperator_eq_fourier]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (S.averagingOrbit_integrable hN x)

theorem averagedFourierOperator_adjoint_continuous (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (y : H) :
    Continuous (fun ξ => star (S.averagedFourierOperator N hN ξ) y) := by
  simp only [averagedFourierOperator_adjoint]
  exact (S.adjoint.averagedFourierOperator_continuous N hN y).comp continuous_neg

theorem averagedFourierOperator_memLp (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (x : H) :
    MemLp (fun ξ => S.averagedFourierOperator N hN ξ x) 2 := by
  exact (memLp_two_iff_integrable_sq_norm
    (S.averagedFourierOperator_continuous N hN x).aestronglyMeasurable).mpr
      (S.averagedFourierOperator_integrable_energy N hN x)

theorem averagedFourierOperator_adjoint_memLp (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (y : H) :
    MemLp (fun ξ => star (S.averagedFourierOperator N hN ξ) y) 2 := by
  exact (memLp_two_iff_integrable_sq_norm
    (S.averagedFourierOperator_adjoint_continuous N hN y).aestronglyMeasurable).mpr
      (S.averagedFourierOperator_adjoint_integrable_energy N hN y)

theorem averagedFourierOperator_integrable_norm_product (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (x y : H) :
    Integrable (fun ξ => ‖S.averagedFourierOperator N hN ξ x‖ *
      ‖star (S.averagedFourierOperator N hN ξ) y‖) :=
  (S.averagedFourierOperator_memLp N hN x).norm.integrable_mul
    (S.averagedFourierOperator_adjoint_memLp N hN y).norm

/-- Cauchy--Schwarz uses both independently proved Plancherel energy bounds. -/
theorem averagedFourierOperator_integral_norm_product_le (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (x y : H) :
    (∫ ξ, ‖S.averagedFourierOperator N hN ξ x‖ *
      ‖star (S.averagedFourierOperator N hN ξ) y‖) ≤ M ^ 2 * ‖x‖ * ‖y‖ := by
  have hx := S.averagedFourierOperator_memLp N hN x
  have hy := S.averagedFourierOperator_adjoint_memLp N hN y
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hx) (by simpa using hy)
  simp only [← Real.sqrt_eq_rpow, Real.rpow_two] at hcs
  have hxe : Real.sqrt (∫ ξ, ‖S.averagedFourierOperator N hN ξ x‖ ^ 2) ≤ M * ‖x‖ := by
    apply (Real.sqrt_le_left (mul_nonneg S.bound_nonneg (norm_nonneg x))).mpr
    simpa only [mul_pow] using S.averagedFourierOperator_energy_le N hN x
  have hye : Real.sqrt (∫ ξ, ‖star (S.averagedFourierOperator N hN ξ) y‖ ^ 2) ≤ M * ‖y‖ := by
    apply (Real.sqrt_le_left (mul_nonneg S.bound_nonneg (norm_nonneg y))).mpr
    simpa only [mul_pow] using S.averagedFourierOperator_adjoint_energy_le N hN y
  calc
    _ ≤ _ := hcs
    _ ≤ (M * ‖x‖) * (M * ‖y‖) := mul_le_mul hxe hye
      (Real.sqrt_nonneg _) (mul_nonneg S.bound_nonneg (norm_nonneg x))
    _ = _ := by ring

/-- Pointwise domination of the finite reconstructed scalar pairing. -/
theorem norm_averagedFourier_pairing_sum_le (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (J : Finset ℕ) (b : ℕ → ℝ → ℂ)
    {C : ℝ} (hbudget : ∀ ξ, ∑ j ∈ J, ‖b j ξ‖ ≤ C) (ξ : ℝ) (x y : H) :
    ‖∑ j ∈ J, b j ξ * inner ℂ (star (S.averagedFourierOperator N hN ξ) y)
      (S.op (j * N) (S.averagedFourierOperator N hN ξ x))‖ ≤
        (M * C) * (‖S.averagedFourierOperator N hN ξ x‖ *
          ‖star (S.averagedFourierOperator N hN ξ) y‖) := by
  let U := S.averagedFourierOperator N hN ξ
  have hnon : 0 ≤ M * (‖U x‖ * ‖star U y‖) :=
    mul_nonneg S.bound_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    _ ≤ ∑ j ∈ J, ‖b j ξ‖ * (M * (‖U x‖ * ‖star U y‖)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ ‖star U y‖ * ‖S.op (j * N) (U x)‖ := norm_inner_le_norm _ _
        _ ≤ ‖star U y‖ * (M * ‖U x‖) := mul_le_mul_of_nonneg_left
          (((S.op (j * N)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (S.bound _ (by positivity)) (norm_nonneg _)))
          (norm_nonneg _)
        _ = _ := by ring
    _ = (∑ j ∈ J, ‖b j ξ‖) * (M * (‖U x‖ * ‖star U y‖)) :=
      (Finset.sum_mul ..).symm
    _ ≤ C * (M * (‖U x‖ * ‖star U y‖)) :=
      mul_le_mul_of_nonneg_right (hbudget ξ) hnon
    _ = _ := by dsimp [U]; ring

theorem averagedFourier_pairing_sum_integrable (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (J : Finset ℕ) (b : ℕ → ℝ → ℂ)
    (hb : ∀ j ∈ J, Continuous (b j)) {C : ℝ}
    (hbudget : ∀ ξ, ∑ j ∈ J, ‖b j ξ‖ ≤ C) (x y : H) :
    Integrable (fun ξ => ∑ j ∈ J, b j ξ *
      inner ℂ (star (S.averagedFourierOperator N hN ξ) y)
        (S.op (j * N) (S.averagedFourierOperator N hN ξ x))) := by
  apply Integrable.mono'
    ((S.averagedFourierOperator_integrable_norm_product N hN x y).const_mul (M * C))
  · apply Continuous.aestronglyMeasurable
    apply continuous_finsetSum
    intro j hj
    exact (hb j hj).mul ((S.averagedFourierOperator_adjoint_continuous N hN y).inner
      ((S.op (j * N)).continuous.comp (S.averagedFourierOperator_continuous N hN x)))
  · exact Filter.Eventually.of_forall fun ξ =>
      S.norm_averagedFourier_pairing_sum_le N hN J b hbudget ξ x y

/-- Once a finite scalar reconstruction is supplied, its uniform frequency
budget gives the operator bound with exactly three factors of `M`. -/
theorem averagedFourier_reconstruction_norm_le (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (J : Finset ℕ) (b : ℕ → ℝ → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hbudget : ∀ ξ, ∑ j ∈ J, ‖b j ξ‖ ≤ C)
    (B : H →L[ℂ] H)
    (hrep : ∀ x y, inner ℂ y (B x) = ∫ ξ, ∑ j ∈ J, b j ξ *
      inner ℂ (star (S.averagedFourierOperator N hN ξ) y)
        (S.op (j * N) (S.averagedFourierOperator N hN ξ x))) :
    ‖B‖ ≤ M ^ 3 * C := by
  have hpair (x y : H) : ‖inner ℂ y (B x)‖ ≤ (M ^ 3 * C) * ‖x‖ * ‖y‖ := by
    rw [hrep]
    calc
      _ ≤ ∫ ξ, (M * C) * (‖S.averagedFourierOperator N hN ξ x‖ *
          ‖star (S.averagedFourierOperator N hN ξ) y‖) :=
        norm_integral_le_of_norm_le
          ((S.averagedFourierOperator_integrable_norm_product N hN x y).const_mul _)
          (Filter.Eventually.of_forall fun ξ =>
            S.norm_averagedFourier_pairing_sum_le N hN J b hbudget ξ x y)
      _ = (M * C) * ∫ ξ, ‖S.averagedFourierOperator N hN ξ x‖ *
          ‖star (S.averagedFourierOperator N hN ξ) y‖ := integral_const_mul _ _
      _ ≤ (M * C) * (M ^ 2 * ‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_left
        (S.averagedFourierOperator_integral_norm_product_le N hN x y)
        (mul_nonneg S.bound_nonneg hC)
      _ = _ := by ring
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (pow_nonneg S.bound_nonneg _) hC)
  intro x
  have hh := hpair x (B x)
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)] at hh
  by_cases hz : ‖B x‖ = 0
  · rw [hz]
    exact mul_nonneg (mul_nonneg (pow_nonneg S.bound_nonneg _) hC) (norm_nonneg _)
  · nlinarith [norm_pos_iff.mpr (norm_ne_zero_iff.mp hz)]

end ProofProject.BoundedSemigroup
