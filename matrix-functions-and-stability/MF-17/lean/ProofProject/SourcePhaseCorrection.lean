import ProofProject.SourcePhaseDefs

/-!
# Quantitative inward phase correction on the upper semicircle

The exact source correction lies strictly between zero and the sector angle.
Its lower bound has the endpoint order `min(θ,π-θ)^ν`, with an explicit positive
constant depending only on `α`. Reflection makes the two endpoint bounds the
same statement.
-/

noncomputable section

namespace ProofProject

/-- An explicit coefficient for the endpoint lower bound. -/
def sourcePhaseCorrectionConstant (α : ℝ) : ℝ :=
  (α / 2) * (2 / Real.pi) ^ sourceWeightNu α *
    Real.sin (sourceWeightNu α * Real.pi / 4)

lemma sourcePhaseCorrectionConstant_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < sourcePhaseCorrectionConstant α := by
  have hν0 := sourceWeightNu_pos hα1
  have hν1 := sourceWeightNu_lt_half hα0
  have hs : 0 < Real.sin (sourceWeightNu α * Real.pi / 4) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  unfold sourcePhaseCorrectionConstant
  exact mul_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos (by positivity) _)) hs

/-- Reflection swaps the two positive terms in the exact correction. -/
lemma sourcePhaseCorrection_reflect (α θ : ℝ) :
    sourcePhaseCorrection α (Real.pi - θ) = sourcePhaseCorrection α θ := by
  have hhalf : (Real.pi - θ) / 2 = Real.pi / 2 - θ / 2 := by ring
  simp only [sourcePhaseCorrection, sub_sub_cancel, hhalf,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

/-- All geometric factors in the correction are positive on the open
upper semicircle. -/
lemma sourcePhaseCorrection_factors_pos {α θ : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    0 < Real.sin (θ / 2) ∧ 0 < Real.cos (θ / 2) ∧
      0 < Real.sin (sourceWeightNu α * ((Real.pi - θ) / 2)) ∧
      0 < Real.sin (sourceWeightNu α * (θ / 2)) := by
  have hν0 := sourceWeightNu_pos hα1
  have hν1 := sourceWeightNu_lt_half hα0
  have ht : 0 < (Real.pi - θ) / 2 := by linarith
  refine ⟨Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]),
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩, ?_, ?_⟩
  · apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hν0 ht)
    nlinarith [Real.pi_pos]
  · apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hν0 (by linarith))
    nlinarith [Real.pi_pos]

lemma sourcePhaseCorrection_pos {α θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) : 0 < sourcePhaseCorrection α θ := by
  obtain ⟨hs, hc, hs₁, hs₂⟩ := sourcePhaseCorrection_factors_pos hα0 hα1 hθ0 hθπ
  unfold sourcePhaseCorrection
  exact mul_pos (by positivity) (add_pos
    (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hs₁)
    (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hs₂))

/-- The sine factors are at most their arguments, and both radii are at most
two. This gives the source's uniform correction budget. -/
lemma sourcePhaseCorrection_le_budget {α θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    sourcePhaseCorrection α θ ≤
      (α / 4) * (2 : ℝ) ^ sourceWeightNu α * sourceWeightNu α * Real.pi := by
  have hν0 := sourceWeightNu_pos hα1
  obtain ⟨hs, hc, hs₁, hs₂⟩ := sourcePhaseCorrection_factors_pos hα0 hα1 hθ0 hθπ
  have hp₁ : (2 * Real.sin (θ / 2)) ^ sourceWeightNu α ≤ (2 : ℝ) ^ sourceWeightNu α :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [Real.sin_le_one (θ / 2)]) hν0.le
  have hp₂ : (2 * Real.cos (θ / 2)) ^ sourceWeightNu α ≤ (2 : ℝ) ^ sourceWeightNu α :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [Real.cos_le_one (θ / 2)]) hν0.le
  have ht₁ := mul_le_mul hp₁
    (Real.sin_le (show 0 ≤ sourceWeightNu α * ((Real.pi - θ) / 2) by positivity))
    hs₁.le (Real.rpow_nonneg (by norm_num) _)
  have ht₂ := mul_le_mul hp₂
    (Real.sin_le (show 0 ≤ sourceWeightNu α * (θ / 2) by positivity))
    hs₂.le (Real.rpow_nonneg (by norm_num) _)
  calc
    _ ≤ 2 * (α / 4) *
        ((2 : ℝ) ^ sourceWeightNu α * (sourceWeightNu α * ((Real.pi - θ) / 2)) +
          (2 : ℝ) ^ sourceWeightNu α * (sourceWeightNu α * (θ / 2))) :=
      mul_le_mul_of_nonneg_left (add_le_add ht₁ ht₂) (by positivity)
    _ = _ := by ring

theorem sourcePhaseCorrection_lt_half_angle {α θ : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    sourcePhaseCorrection α θ < Real.pi * α / 2 :=
  (sourcePhaseCorrection_le_budget hα0 hα1 hθ0 hθπ).trans_lt
    (source_argument_correction_upper hα0 hα1)

/-- The first correction term controls the distance from the endpoint zero
throughout the first half of the upper semicircle. -/
lemma sourcePhaseCorrection_lower_first_half {α θ : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθhalf : θ ≤ Real.pi / 2) :
    sourcePhaseCorrectionConstant α * θ ^ sourceWeightNu α ≤ sourcePhaseCorrection α θ := by
  have hθπ : θ < Real.pi := by linarith [Real.pi_pos]
  have hν0 := sourceWeightNu_pos hα1
  have hν1 := sourceWeightNu_lt_half hα0
  obtain ⟨hs, hc, hs₁, hs₂⟩ := sourcePhaseCorrection_factors_pos hα0 hα1 hθ0 hθπ
  have hrad : (2 / Real.pi) * θ ≤ 2 * Real.sin (θ / 2) := by
    have hj := Real.mul_le_sin (x := θ / 2) (by linarith) (by linarith)
    nlinarith
  have hpow : (2 / Real.pi) ^ sourceWeightNu α * θ ^ sourceWeightNu α ≤
      (2 * Real.sin (θ / 2)) ^ sourceWeightNu α := by
    rw [← Real.mul_rpow (by positivity) hθ0.le]
    exact Real.rpow_le_rpow (by positivity) hrad hν0.le
  have hsin : Real.sin (sourceWeightNu α * Real.pi / 4) ≤
      Real.sin (sourceWeightNu α * ((Real.pi - θ) / 2)) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
    · nlinarith
  have hsbase : 0 ≤ Real.sin (sourceWeightNu α * Real.pi / 4) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · nlinarith [Real.pi_pos]
  have hfirst := mul_le_mul hpow hsin hsbase
    (Real.rpow_nonneg (by positivity : 0 ≤ 2 * Real.sin (θ / 2)) _)
  have hsecond : 0 ≤ (2 * Real.cos (θ / 2)) ^ sourceWeightNu α *
      Real.sin (sourceWeightNu α * (θ / 2)) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) hs₂.le
  calc
    _ = (α / 2) *
        (((2 / Real.pi) ^ sourceWeightNu α * θ ^ sourceWeightNu α) *
          Real.sin (sourceWeightNu α * Real.pi / 4)) := by
      unfold sourcePhaseCorrectionConstant
      ring
    _ ≤ (α / 2) *
        ((2 * Real.sin (θ / 2)) ^ sourceWeightNu α *
          Real.sin (sourceWeightNu α * ((Real.pi - θ) / 2)) +
          (2 * Real.cos (θ / 2)) ^ sourceWeightNu α *
          Real.sin (sourceWeightNu α * (θ / 2))) :=
      mul_le_mul_of_nonneg_left (hfirst.trans (le_add_of_nonneg_right hsecond)) (by positivity)
    _ = _ := by unfold sourcePhaseCorrection; ring

/-- Uniform endpoint-order lower bound, with the same explicit constant near
both endpoints of the upper semicircle. -/
theorem sourcePhaseCorrection_lower {α θ : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    sourcePhaseCorrectionConstant α * (min θ (Real.pi - θ)) ^ sourceWeightNu α ≤
      sourcePhaseCorrection α θ := by
  by_cases hh : θ ≤ Real.pi / 2
  · rw [min_eq_left (by linarith : θ ≤ Real.pi - θ)]
    exact sourcePhaseCorrection_lower_first_half hα0 hα1 hθ0 hh
  · rw [min_eq_right (by linarith : Real.pi - θ ≤ θ)]
    have h := sourcePhaseCorrection_lower_first_half hα0 hα1
      (show 0 < Real.pi - θ by linarith) (show Real.pi - θ ≤ Real.pi / 2 by linarith)
    rwa [sourcePhaseCorrection_reflect] at h

/-- A packaged positive constant and all phase-correction conclusions. -/
theorem sourcePhaseCorrection_bounds {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ : ℝ, 0 < θ → θ < Real.pi →
      0 < sourcePhaseCorrection α θ ∧ sourcePhaseCorrection α θ < Real.pi * α / 2 ∧
        c * (min θ (Real.pi - θ)) ^ sourceWeightNu α ≤ sourcePhaseCorrection α θ := by
  refine ⟨sourcePhaseCorrectionConstant α, sourcePhaseCorrectionConstant_pos hα0 hα1, ?_⟩
  intro θ hθ0 hθπ
  exact ⟨sourcePhaseCorrection_pos hα0 hα1 hθ0 hθπ,
    sourcePhaseCorrection_lt_half_angle hα0 hα1 hθ0 hθπ,
    sourcePhaseCorrection_lower hα0 hα1 hθ0 hθπ⟩

end ProofProject
