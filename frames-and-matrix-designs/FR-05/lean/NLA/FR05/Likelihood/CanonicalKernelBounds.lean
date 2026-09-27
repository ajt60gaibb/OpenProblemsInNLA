import NLA.FR05.Overlap.OverlapCholesky

/-!
# Canonical kernels and comparison bounds

The sections develop `CanonicalKernelBounds`, `KernelComparison`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section CanonicalKernelBounds

open MeasureTheory Complex Real Matrix WithLp


theorem canonicalOverlapLaw_map_fst (K : SourceOverlapMatrix) :
    (canonicalOverlapLaw K).map Prod.fst = standardComplexGaussianTail 2 := by
  rw [canonicalOverlapLaw, Measure.map_map measurable_fst (continuous_canonicalOverlapMap K).measurable]
  change ((standardComplexGaussianTail 2).prod (standardComplexGaussianTail 2)).map Prod.fst = _
  simp

theorem canonicalOverlapLaw_map_snd {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) :
    (canonicalOverlapLaw K).map Prod.snd = standardComplexGaussianTail 2 := by
  let B := (canonicalOverlapColumns K).submatrix id Sum.inr
  have hB : Bᴴ * B = (1 : SourceOverlapMatrix) := by
    dsimp [B]
    rw [Matrix.conjTranspose_submatrix]
    have h := Matrix.submatrix_mul_equiv (canonicalOverlapColumns K)ᴴ
      (canonicalOverlapColumns K) Sum.inr (Equiv.refl (Fin 4)) Sum.inr
    simp only [Equiv.coe_refl] at h
    rw [h, canonicalOverlapColumns_gram hK]
    rfl
  rw [canonicalOverlapLaw_eq_projection,
    Measure.map_map measurable_snd continuous_unpackSourceProjections.measurable,
    Measure.map_map (measurable_snd.comp continuous_unpackSourceProjections.measurable)
      (continuous_gaussianMatrixProjection _).measurable]
  have he : (Prod.snd ∘ unpackSourceProjections) ∘
      gaussianMatrixProjection (canonicalOverlapColumns K) =
      fun x : Signal 4 ↦ Bᴴ *ᵥ star x := by
    funext x
    ext i
    simp [B, gaussianMatrixProjection, unpackSourceProjections, Matrix.mulVec,
      dotProduct, Matrix.conjTranspose_apply, Matrix.submatrix]
  rw [he]
  exact standardComplexGaussianTail_map_orthonormal B hB

theorem integrable_canonical_projectedDensity {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    Integrable (fun p : Signal 2 × Signal 2 ↦ sourceDensity a M p.2) (canonicalOverlapLaw K) := by
  have hm : AEStronglyMeasurable (sourceDensity a M) ((canonicalOverlapLaw K).map Prod.snd) :=
    (measurable_sourceDensity a M).aestronglyMeasurable
  apply (integrable_map_measure hm measurable_snd.aemeasurable).mp
  rw [canonicalOverlapLaw_map_snd hK]
  by_contra hi
  have h := integral_sourceDensity hM a
  rw [integral_undef hi] at h
  norm_num at h

theorem integral_canonical_projectedDensity {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    (∫ p : Signal 2 × Signal 2, sourceDensity a M p.2 ∂canonicalOverlapLaw K) = 1 := by
  have h := integral_map (φ := Prod.snd) (μ := canonicalOverlapLaw K)
    measurable_snd.aemeasurable (f := sourceDensity a M)
    (measurable_sourceDensity a M).aestronglyMeasurable
  rw [canonicalOverlapLaw_map_snd hK, integral_sourceDensity hM a] at h
  exact h.symm

theorem sourceDensityCorrelation_nonneg {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) (a b : SourceDensityKind) (M : ℕ) :
    0 ≤ sourceDensityCorrelation a b M K :=
  integral_nonneg (fun p ↦ overlapGaussianRatio_nonneg hK p.1 p.2)

theorem sourceDensityCorrelation_le_densityBound {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    sourceDensityCorrelation a b M K ≤ sourceDensityBound M := by
  have hi := (integrable_canonical_projectedDensity hM b hK).const_mul (sourceDensityBound M)
  have hm : Measurable (fun p : Signal 2 × Signal 2 ↦
      sourceDensity a M p.1 * sourceDensity b M p.2) :=
    ((measurable_sourceDensity a M).comp measurable_fst).mul
      ((measurable_sourceDensity b M).comp measurable_snd)
  have hle (p : Signal 2 × Signal 2) :
      sourceDensity a M p.1 * sourceDensity b M p.2 ≤ sourceDensityBound M * sourceDensity b M p.2 :=
    mul_le_mul_of_nonneg_right (sourceDensity_le hM a p.1) (sourceDensity_nonneg b M p.2)
  have hprod : Integrable (fun p : Signal 2 × Signal 2 ↦
      sourceDensity a M p.1 * sourceDensity b M p.2) (canonicalOverlapLaw K) := by
    apply hi.mono' hm.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sourceDensity_nonneg a M _) (sourceDensity_nonneg b M _))]
    exact hle p
  rw [sourceDensityCorrelation_eq_integral_canonical hK]
  calc
    _ ≤ ∫ p : Signal 2 × Signal 2, sourceDensityBound M * sourceDensity b M p.2 ∂canonicalOverlapLaw K :=
      integral_mono hprod hi hle
    _ = _ := by rw [integral_const_mul, integral_canonical_projectedDensity hM b hK, mul_one]

theorem sourceDensityCorrelation_polynomial_bound {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    sourceDensityCorrelation a b M K ≤ (Real.exp 1 + 4) * (M : ℝ)^52 := by
  apply (sourceDensityCorrelation_le_densityBound hM a b hK).trans
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by lia)
  have hpow : (1 : ℝ) ≤ (M : ℝ)^52 := one_le_pow₀ hM1
  unfold sourceDensityBound
  nlinarith

end CanonicalKernelBounds

section KernelComparison

open Filter
open scoped Topology

/-- Fifteen reserved factors make the determinant exponent integral. -/
theorem source_tail_factorization {M : ℕ} (hM : 5 ≤ M) (ρ Δ : ℝ) :
    ρ ^ sourceRowCount M * Δ ^ (M - 4) =
      ρ ^ 15 * (ρ ^ 4 * Δ) ^ (M - 5) * Δ := by
  have hN : sourceRowCount M = 15 + 4 * (M - 5) := by
    unfold sourceRowCount
    lia
  have hD : M - 4 = (M - 5) + 1 := by lia
  rw [hN, hD, pow_add, pow_add, pow_one, mul_pow, pow_mul]
  ring

theorem source_tail_bound {M : ℕ} (hM : 5 ≤ M)
    {ρ Δ B a : ℝ} (hρ : 0 ≤ ρ) (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hB : ρ ≤ B) (hkernel : ρ ^ 4 * Δ ≤ Real.exp a) :
    ρ ^ sourceRowCount M * Δ ^ (M - 4) ≤
      B ^ 15 * Real.exp ((M - 5 : ℕ) * a) := by
  have hB0 : 0 ≤ B := hρ.trans hB
  rw [source_tail_factorization hM]
  calc
    _ ≤ B ^ 15 * (Real.exp a) ^ (M - 5) * 1 := by
      gcongr
    _ = _ := by rw [mul_one, ← Real.exp_nat_mul]

/-- The fractional determinant bound (3.13) gives the integer-power tail estimate. -/
theorem source_tail_bound_of_rpow {M : ℕ} (hM : 5 ≤ M)
    {ρ Δ B a : ℝ} (hρ : 0 ≤ ρ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hB : ρ ≤ B) (hkernel : ρ ≤ Real.exp a * Δ ^ (-(1 / 4) : ℝ)) :
    ρ ^ sourceRowCount M * Δ ^ (M - 4) ≤
      B ^ 15 * Real.exp ((M - 5 : ℕ) * (4 * a)) := by
  apply source_tail_bound hM hρ hΔ.le hΔ1 hB
  have hroot : (Δ ^ (-(1 / 4) : ℝ)) ^ 4 * Δ = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΔ.le]
    norm_num
    rw [Real.rpow_neg_one]
    exact inv_mul_cancel₀ hΔ.ne'
  calc
    _ ≤ (Real.exp a * Δ ^ (-(1 / 4) : ℝ)) ^ 4 * Δ := by gcongr
    _ = Real.exp (4 * a) := by
      rw [mul_pow, mul_assoc, hroot, mul_one, ← Real.exp_nat_mul]
      norm_num

/-- Matched quadratic terms leave a quartic error after taking row products. -/
theorem kernel_power_difference_le {a b q x C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haq : |a - (1 + q * x)| ≤ C * x ^ 2)
    (hbq : |b - (1 + q * x)| ≤ C * x ^ 2) (N : ℕ) :
    |a ^ N - b ^ N| ≤ 2 * C * x ^ 2 * N * max a b ^ (N - 1) := by
  have hab : |a - b| ≤ 2 * C * x ^ 2 := by
    calc
      _ = |(a - (1 + q * x)) + ((1 + q * x) - b)| := by ring_nf
      _ ≤ |a - (1 + q * x)| + |(1 + q * x) - b| := abs_add_le _ _
      _ ≤ 2 * C * x ^ 2 := by rw [abs_sub_comm (1 + q * x) b]; linarith
  calc
    _ ≤ |a - b| * N * max |a| |b| ^ (N - 1) := abs_pow_sub_pow_le a b N
    _ ≤ _ := by
      rw [abs_of_nonneg ha, abs_of_nonneg hb]
      gcongr

/-- Every fixed polynomial times an exponentially decaying tail is o(1/M). -/
theorem polynomial_exp_tail_le_inv (C c : ℝ) (hc : 0 < c) (k : ℕ) :
    ∃ D : ℕ, ∀ M : ℕ, D ≤ M →
      C * (M : ℝ) ^ k * Real.exp (-c * M) ≤ 1 / M := by
  have ht : Tendsto (fun M : ℕ ↦ C * ((M : ℝ) ^ (k + 1) * Real.exp (-c * M)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k + 1 : ℕ) : ℝ) c hc).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, Real.rpow_natCast, mul_zero] using h.const_mul C
  obtain ⟨D, hD⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds zero_lt_one))
  refine ⟨max D 1, fun M hM ↦ ?_⟩
  have hm : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
    ((le_max_right D 1).trans hM))
  apply (le_div_iff₀ hm).mpr
  have hh := (hD M ((le_max_left D 1).trans hM)).le
  rw [pow_succ] at hh
  nlinarith only [hh]

end KernelComparison

end NLA.FR05
