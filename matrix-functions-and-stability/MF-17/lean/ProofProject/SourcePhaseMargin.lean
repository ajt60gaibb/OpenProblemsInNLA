import ProofProject.SourcePhaseCorrection
import ProofProject.SourcePhasePolar
import ProofProject.CosineMargin

/-!
# The positive boundary phase margin of the actual source factor

The exact principal-power phase identity and the positive inward correction
give the endpoint-order lower bound for the source margin. The constant
depends only on the exponent, hence only on `M` at the target exponent.
-/

noncomputable section

namespace ProofProject

/-- The explicit coefficient in the source margin's endpoint lower bound. -/
def sourcePhaseMarginConstant (α : ℝ) : ℝ :=
  (4 / Real.pi) * Real.cos (Real.pi * α / 2) *
    Real.sin ((Real.pi * α / 2) / 2) * sourcePhaseCorrectionConstant α

lemma sourcePhaseMarginConstant_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < sourcePhaseMarginConstant α := by
  have hβ0 : 0 < Real.pi * α / 2 := by positivity
  have hβπ : Real.pi * α / 2 < Real.pi / 2 := by nlinarith [Real.pi_pos]
  exact mul_pos (cosine_margin_coefficient_pos hβ0 hβπ)
    (sourcePhaseCorrectionConstant_pos hα0 hα1)

/-- Quantitative endpoint control for the margin of the exact boundary factor. -/
theorem sourcePhaseMargin_lower {α θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    sourcePhaseMarginConstant α * (min θ (Real.pi - θ)) ^ sourceWeightNu α ≤
      sourcePhaseMargin α θ := by
  have hβ0 : 0 < Real.pi * α / 2 := by positivity
  have hβπ : Real.pi * α / 2 < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hcoeff := cosine_margin_coefficient_pos hβ0 hβπ
  have hE0 := sourcePhaseCorrection_pos hα0 hα1 hθ0 hθπ
  have hEβ := sourcePhaseCorrection_lt_half_angle hα0 hα1 hθ0 hθπ
  have hcorrection := sourcePhaseCorrection_lower hα0 hα1 hθ0 hθπ
  have hcos := cosine_margin_lower hβ0 hβπ hE0.le hEβ.le
  rw [sourcePhaseMargin, sourceBoundaryPhase_re α hθ0 hθπ]
  calc
    _ = ((4 / Real.pi) * Real.cos (Real.pi * α / 2) *
        Real.sin ((Real.pi * α / 2) / 2)) *
        (sourcePhaseCorrectionConstant α * (min θ (Real.pi - θ)) ^ sourceWeightNu α) := by
      unfold sourcePhaseMarginConstant
      ring
    _ ≤ ((4 / Real.pi) * Real.cos (Real.pi * α / 2) *
        Real.sin ((Real.pi * α / 2) / 2)) * sourcePhaseCorrection α θ :=
      mul_le_mul_of_nonneg_left hcorrection hcoeff.le
    _ ≤ _ := hcos

/-- The margin is strictly positive at every nonexceptional upper-half point. -/
theorem sourcePhaseMargin_pos {α θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) : 0 < sourcePhaseMargin α θ := by
  have hmin : 0 < min θ (Real.pi - θ) := lt_min hθ0 (sub_pos.mpr hθπ)
  exact (mul_pos (sourcePhaseMarginConstant_pos hα0 hα1)
    (Real.rpow_pos_of_pos hmin _)).trans_le (sourcePhaseMargin_lower hα0 hα1 hθ0 hθπ)

/-- A uniform positive coefficient controls the whole open upper semicircle. -/
theorem sourcePhaseMargin_bounds {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ : ℝ, 0 < θ → θ < Real.pi →
      0 < sourcePhaseMargin α θ ∧
      c * (min θ (Real.pi - θ)) ^ sourceWeightNu α ≤ sourcePhaseMargin α θ := by
  refine ⟨sourcePhaseMarginConstant α, sourcePhaseMarginConstant_pos hα0 hα1, ?_⟩
  intro θ hθ0 hθπ
  exact ⟨sourcePhaseMargin_pos hα0 hα1 hθ0 hθπ,
    sourcePhaseMargin_lower hα0 hα1 hθ0 hθπ⟩

/-- The lower-semicircle margin is the reflected upper-semicircle margin. -/
lemma sourcePhaseMargin_neg (α : ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    sourcePhaseMargin α (-θ) = sourcePhaseMargin α θ := by
  rw [sourcePhaseMargin, sourcePhaseMargin, sourceBoundaryPhase_re_neg α hθ0 hθπ]

/-- The same quantitative bound on both halves of the principal circle, with
the two exceptional endpoints omitted. -/
theorem sourcePhaseMargin_lower_abs {α θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) :
    sourcePhaseMarginConstant α * (min |θ| (Real.pi - |θ|)) ^ sourceWeightNu α ≤
      sourcePhaseMargin α θ := by
  by_cases hθ : 0 ≤ θ
  · simp only [abs_of_nonneg hθ] at hθ0 hθπ ⊢
    exact sourcePhaseMargin_lower hα0 hα1 hθ0 hθπ
  · have hθneg : θ < 0 := lt_of_not_ge hθ
    simp only [abs_of_neg hθneg] at hθ0 hθπ ⊢
    have hreflect : sourcePhaseMargin α θ = sourcePhaseMargin α (-θ) := by
      simpa only [neg_neg] using sourcePhaseMargin_neg α hθ0 hθπ
    rw [hreflect]
    exact sourcePhaseMargin_lower hα0 hα1 hθ0 hθπ

theorem sourcePhaseMargin_pos_abs {α θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) : 0 < sourcePhaseMargin α θ := by
  have hmin : 0 < min |θ| (Real.pi - |θ|) := lt_min hθ0 (sub_pos.mpr hθπ)
  exact (mul_pos (sourcePhaseMarginConstant_pos hα0 hα1)
    (Real.rpow_pos_of_pos hmin _)).trans_le (sourcePhaseMargin_lower_abs hα0 hα1 hθ0 hθπ)

/-- At the exact target exponent, the center of the phase sector is `1/M`. -/
lemma sourcePhaseMargin_growthExponent (M θ : ℝ) (hM : 1 ≤ M) :
    sourcePhaseMargin (growthExponent M) θ =
      2 * (1 / M) * ((sourceBoundaryPhase (growthExponent M) θ).re - 1 / M) := by
  rw [sourcePhaseMargin, cos_growthExponent_half_angle hM]

/-- The endpoint-order lower bound with the source's exact parameter `μ=1/M`. -/
theorem sourcePhaseMargin_growthExponent_lower {M θ : ℝ} (hM : 1 < M)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    sourcePhaseMarginConstant (growthExponent M) *
        (min θ (Real.pi - θ)) ^ sourceWeightNu (growthExponent M) ≤
      2 * (1 / M) * ((sourceBoundaryPhase (growthExponent M) θ).re - 1 / M) := by
  rw [← sourcePhaseMargin_growthExponent M θ hM.le]
  exact sourcePhaseMargin_lower (growthExponent_pos hM) (growthExponent_mem_Ioo hM).2 hθ0 hθπ

lemma sourcePhaseMarginConstant_growthExponent_pos {M : ℝ} (hM : 1 < M) :
    0 < sourcePhaseMarginConstant (growthExponent M) :=
  sourcePhaseMarginConstant_pos (growthExponent_pos hM) (growthExponent_mem_Ioo hM).2

end ProofProject
