import ProofProject.SourceMarginIntegrability

/-!
# The actual source phase on angular measure

All assertions are for the ordinary restricted angular measure. The three
exceptional angles are removed only almost everywhere. The two reciprocal
weights are controlled by one finite integral depending only on the exponent.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

lemma measurable_sourceBoundaryPhase (α : ℝ) : Measurable (sourceBoundaryPhase α) := by
  unfold sourceBoundaryPhase
  have hm := (measurable_sourceWeightFactor α).comp measurable_sourceCircle
  exact (continuous_star.measurable.comp hm).div hm

lemma ae_sourceCircle_regular :
    ∀ᵐ θ : ℝ ∂(volume.restrict (Set.Icc (-Real.pi) Real.pi)),
      0 < |θ| ∧ |θ| < Real.pi := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (volume.restrict (Set.Icc (-Real.pi) Real.pi)).ae_ne 0,
    (volume.restrict (Set.Icc (-Real.pi) Real.pi)).ae_ne Real.pi,
    (volume.restrict (Set.Icc (-Real.pi) Real.pi)).ae_ne (-Real.pi)] with θ hθ h0 hp hn
  exact ⟨abs_pos.mpr h0, abs_lt.mpr
    ⟨lt_of_le_of_ne hθ.1 hn.symm, lt_of_le_of_ne hθ.2 hp⟩⟩

lemma sourceWeightFactor_circle_ne_zero_abs (α : ℝ) {θ : ℝ}
    (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) :
    sourceWeightFactor α (sourceCircle θ) ≠ 0 := by
  by_cases hθ : 0 ≤ θ
  · rw [abs_of_nonneg hθ] at hθ0 hθπ
    exact sourceWeightFactor_circle_ne_zero α hθ0 hθπ
  · have hneg : θ < 0 := lt_of_not_ge hθ
    rw [abs_of_neg hneg] at hθ0 hθπ
    have hreflect := sourceWeightFactor_circle_neg α hθ0 hθπ
    rw [neg_neg] at hreflect
    rw [hreflect]
    exact (map_ne_zero (starRingEnd ℂ)).mpr (sourceWeightFactor_circle_ne_zero α hθ0 hθπ)

lemma sourceBoundaryPhase_norm (α : ℝ) {θ : ℝ}
    (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) :
    ‖sourceBoundaryPhase α θ‖ = 1 := by
  rw [sourceBoundaryPhase, norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr (sourceWeightFactor_circle_ne_zero_abs α hθ0 hθπ))

lemma sourceBoundaryPhase_ae_norm (α : ℝ) :
    ∀ᵐ θ : ℝ ∂(volume.restrict (Set.Icc (-Real.pi) Real.pi)),
      ‖sourceBoundaryPhase α θ‖ = 1 :=
  ae_sourceCircle_regular.mono fun _ hθ => sourceBoundaryPhase_norm α hθ.1 hθ.2

lemma sourcePhaseMargin_ae_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ᵐ θ : ℝ ∂(volume.restrict (Set.Icc (-Real.pi) Real.pi)),
      0 < sourcePhaseMargin α θ :=
  ae_sourceCircle_regular.mono fun _ hθ => sourcePhaseMargin_pos_abs hα0 hα1 hθ.1 hθ.2

/-- The exact inverse-parameter version of the source margin formula. -/
lemma sourcePhaseMargin_growthExponent_inv (M θ : ℝ) (hM : 1 ≤ M) :
    sourcePhaseMargin (growthExponent M) θ =
      2 * M⁻¹ * ((sourceBoundaryPhase (growthExponent M) θ).re - M⁻¹) := by
  simpa only [one_div] using sourcePhaseMargin_growthExponent M θ hM

/-- This identity also bounds both the margin and the centered phase. -/
lemma sourceBoundaryPhase_centered_norm_sq {M θ : ℝ} (hM : 1 ≤ M)
    (hg : ‖sourceBoundaryPhase (growthExponent M) θ‖ = 1) :
    ‖sourceBoundaryPhase (growthExponent M) θ - (M⁻¹ : ℝ)‖ ^ 2 =
      1 - (M⁻¹) ^ 2 - sourcePhaseMargin (growthExponent M) θ := by
  rw [sourcePhaseMargin_growthExponent_inv M θ hM, Complex.sq_norm, Complex.normSq_sub,
    Complex.normSq_eq_norm_sq, hg]
  simp only [Complex.normSq_ofReal, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, one_pow]
  ring

/-- All pointwise phase hypotheses needed in the energy estimate hold outside
the three null exceptional angles. -/
theorem sourcePhaseMeasure_bounds {M : ℝ} (hM : 1 < M) :
    ∀ᵐ θ : ℝ ∂(volume.restrict (Set.Icc (-Real.pi) Real.pi)),
      ‖sourceBoundaryPhase (growthExponent M) θ‖ = 1 ∧
      0 < sourcePhaseMargin (growthExponent M) θ ∧
      sourcePhaseMargin (growthExponent M) θ ≤ 1 - (M⁻¹) ^ 2 ∧
      1 - (M⁻¹) ^ 2 ≤ 1 ∧
      ‖sourceBoundaryPhase (growthExponent M) θ - (M⁻¹ : ℝ)‖ ^ 2 ≤ 1 := by
  filter_upwards [sourceBoundaryPhase_ae_norm (growthExponent M),
    sourcePhaseMargin_ae_pos (growthExponent_pos hM) (growthExponent_mem_Ioo hM).2] with θ hg hd
  have hid := sourceBoundaryPhase_centered_norm_sq hM.le hg
  have hsq := sq_nonneg ‖sourceBoundaryPhase (growthExponent M) θ - (M⁻¹ : ℝ)‖
  have hinv := sq_nonneg (M⁻¹)
  exact ⟨hg, hd, by linarith, by linarith, by linarith⟩

/-- The source's finite reciprocal-margin integral, in raw angular measure. -/
def sourcePhaseQuotientIntegral (α : ℝ) : ℝ :=
  ∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi,
    (1 + ‖sourceWeightFactor α (sourceCircle θ)‖ ^ 2) / sourcePhaseMargin α θ

lemma sourcePhaseQuotientIntegral_nonneg {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 ≤ sourcePhaseQuotientIntegral α := by
  apply integral_nonneg_of_ae
  filter_upwards [sourcePhaseMargin_ae_pos hα0 hα1] with θ hθ
  exact div_nonneg (by positivity) hθ.le

lemma sourcePhaseMargin_inv_le_quotient {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ᵐ θ : ℝ ∂(volume.restrict (Set.Icc (-Real.pi) Real.pi)),
      1 / sourcePhaseMargin α θ ≤
        (1 + ‖sourceWeightFactor α (sourceCircle θ)‖ ^ 2) / sourcePhaseMargin α θ := by
  filter_upwards [sourcePhaseMargin_ae_pos hα0 hα1] with θ hθ
  exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) hθ.le

lemma sourcePhaseMargin_weighted_inv_le_quotient {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ᵐ θ : ℝ ∂(volume.restrict (Set.Icc (-Real.pi) Real.pi)),
      ‖sourceWeightFactor α (sourceCircle θ)‖ ^ 2 / sourcePhaseMargin α θ ≤
        (1 + ‖sourceWeightFactor α (sourceCircle θ)‖ ^ 2) / sourcePhaseMargin α θ := by
  filter_upwards [sourcePhaseMargin_ae_pos hα0 hα1] with θ hθ
  exact div_le_div_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hθ.le

lemma sourcePhaseMargin_inv_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Integrable (fun θ => 1 / sourcePhaseMargin α θ)
      (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
  apply (source_margin_quotient_integrable hα0 hα1).mono'
    (measurable_const.div (measurable_sourcePhaseMargin α)).aestronglyMeasurable
  filter_upwards [sourcePhaseMargin_ae_pos hα0 hα1,
    sourcePhaseMargin_inv_le_quotient hα0 hα1] with θ hd hle
  simp only [Pi.div_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one hd.le)]
  exact hle

lemma sourcePhaseMargin_weighted_inv_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Integrable (fun θ => ‖sourceWeightFactor α (sourceCircle θ)‖ ^ 2 / sourcePhaseMargin α θ)
      (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
  have hw := (((measurable_sourceWeightFactor α).comp measurable_sourceCircle).norm).pow_const 2
  apply (source_margin_quotient_integrable hα0 hα1).mono'
    (hw.div (measurable_sourcePhaseMargin α)).aestronglyMeasurable
  filter_upwards [sourcePhaseMargin_ae_pos hα0 hα1,
    sourcePhaseMargin_weighted_inv_le_quotient hα0 hα1] with θ hd hle
  simp only [Pi.div_apply, Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hd.le)]
  exact hle

lemma integral_inv_sourcePhaseMargin_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, 1 / sourcePhaseMargin α θ) ≤
      sourcePhaseQuotientIntegral α :=
  integral_mono_ae (sourcePhaseMargin_inv_integrable hα0 hα1)
    (source_margin_quotient_integrable hα0 hα1) (sourcePhaseMargin_inv_le_quotient hα0 hα1)

lemma integral_weighted_inv_sourcePhaseMargin_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi,
      ‖sourceWeightFactor α (sourceCircle θ)‖ ^ 2 / sourcePhaseMargin α θ) ≤
      sourcePhaseQuotientIntegral α :=
  integral_mono_ae (sourcePhaseMargin_weighted_inv_integrable hα0 hα1)
    (source_margin_quotient_integrable hα0 hα1) (sourcePhaseMargin_weighted_inv_le_quotient hα0 hα1)

end ProofProject
