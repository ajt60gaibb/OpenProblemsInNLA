import ProofProject.GrowthRate
import ProofProject.SourceWeightFactor

/-! The source angular parameters retain the target's exact dependence on M. -/

noncomputable section

namespace ProofProject

/-- The sector half-angle in the weight construction is exactly arccos(1/M). -/
lemma growthExponent_half_angle (M : ℝ) :
    Real.pi * growthExponent M / 2 = Real.arccos (1 / M) := by
  unfold growthExponent
  field_simp

lemma cos_growthExponent_half_angle {M : ℝ} (hM : 1 ≤ M) :
    Real.cos (Real.pi * growthExponent M / 2) = 1 / M := by
  rw [growthExponent_half_angle]
  have hM0 : 0 < M := by linarith
  have hμ : 0 < 1 / M := one_div_pos.mpr hM0
  exact Real.cos_arccos (by linarith) ((div_le_one hM0).mpr hM)

lemma sin_growthExponent_half_angle (M : ℝ) :
    Real.sin (Real.pi * growthExponent M / 2) = Real.sqrt (1 - (1 / M) ^ 2) := by
  rw [growthExponent_half_angle, Real.sin_arccos]

lemma sourceWeightNu_add_lt_one {α : ℝ} (hα : α < 1) :
    α + sourceWeightNu α < 1 := by
  unfold sourceWeightNu
  linarith

/-- The largest possible argument correction is strictly smaller than the
sector angle. This bound is used before the endpoint asymptotics of the margin. -/
lemma source_argument_correction_upper {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (α / 4) * (2 : ℝ) ^ sourceWeightNu α * sourceWeightNu α * Real.pi <
      Real.pi * α / 2 := by
  have hν0 := sourceWeightNu_pos hα1
  have hν := sourceWeightNu_lt_half hα0
  have hp : (2 : ℝ) ^ sourceWeightNu α ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show sourceWeightNu α ≤ 1 by linarith)
  calc
    _ ≤ (α / 4) * 2 * sourceWeightNu α * Real.pi := by gcongr
    _ < Real.pi * α / 2 := by
      have hh := mul_lt_mul_of_pos_right (show sourceWeightNu α < 1 by linarith)
        (mul_pos Real.pi_pos hα0)
      nlinarith

/-- Both exponents governing the boundary singularities are integrable. -/
lemma sourceWeight_exponent_conditions {M : ℝ} (hM : 1 < M) :
    0 < sourceWeightNu (growthExponent M) ∧
    sourceWeightNu (growthExponent M) < 1 / 2 ∧
    growthExponent M + sourceWeightNu (growthExponent M) < 1 := by
  exact ⟨sourceWeightNu_pos (growthExponent_mem_Ioo hM).2,
    sourceWeightNu_lt_half (growthExponent_pos hM),
    sourceWeightNu_add_lt_one (growthExponent_mem_Ioo hM).2⟩

end ProofProject
