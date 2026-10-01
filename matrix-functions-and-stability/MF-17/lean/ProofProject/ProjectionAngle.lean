import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The sharp angle bound implied by a uniformly bounded projection onto a line. -/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

set_option backward.isDefEq.respectTransparency.types false in
/-- The exact squared angle estimate. The hypothesis bounds the first component
along every complex translate in the direction of the second component. -/
theorem projectionAngle_sq {K : ℝ} (hK : 1 ≤ K) (u v : H)
    (h : ∀ t : ℂ, ‖u‖ ≤ K * ‖u + t • v‖) :
    ‖inner ℂ u v‖ ^ 2 ≤ (1 - K⁻¹ ^ 2) * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  by_cases hv : v = 0
  · simp [hv]
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hv2 : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero _ hvn
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let c : ℂ := inner ℂ v u / ((‖v‖ ^ 2 : ℝ) : ℂ)
  let w : H := u - c • v
  have hself : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow] using!
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v)
  have horth : inner ℂ v w = 0 := by
    dsimp [w, c]
    rw [inner_sub_right, inner_smul_right, hself,
      div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hv2), sub_self]
  have hsplit : u = c • v + w := by dsimp [w]; abel
  have hpyth : ‖u‖ ^ 2 = ‖c • v‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [hsplit]
    have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
      (c • v) w (by rw [inner_smul_left, horth, mul_zero])
    simpa only [pow_two] using hh
  have hc : ‖c • v‖ ^ 2 * ‖v‖ ^ 2 = ‖inner ℂ u v‖ ^ 2 := by
    rw [norm_smul]
    dsimp [c]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      mul_pow, div_pow, norm_inner_symm (𝕜 := ℂ) v u]
    field_simp
  have hb : ‖u‖ ≤ K * ‖w‖ := by
    simpa only [w, neg_smul, sub_eq_add_neg] using h (-c)
  have hsq : ‖u‖ ^ 2 ≤ K ^ 2 * ‖w‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg u) hb 2
  have hdiv : K⁻¹ ^ 2 * ‖u‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    calc
      K⁻¹ ^ 2 * ‖u‖ ^ 2 = ‖u‖ ^ 2 / K ^ 2 := by rw [inv_pow]; ring
      _ ≤ ‖w‖ ^ 2 := (div_le_iff₀ (sq_pos_of_pos hKpos)).2 (by nlinarith [hsq])
  have hm := mul_le_mul_of_nonneg_right hdiv (sq_nonneg ‖v‖)
  have hp := congrArg (fun r : ℝ => r * ‖v‖ ^ 2) hpyth
  nlinarith [hc, hm, hp]

/-- The unsquared projection angle estimate, with its exact sharp constant. -/
theorem projectionAngle {K : ℝ} (hK : 1 ≤ K) (u v : H)
    (h : ∀ t : ℂ, ‖u‖ ≤ K * ‖u + t • v‖) :
    ‖inner ℂ u v‖ ≤ Real.sqrt (1 - K⁻¹ ^ 2) * ‖u‖ * ‖v‖ := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hinv : 0 ≤ K⁻¹ := inv_nonneg.mpr hKpos.le
  have hinv1 : K⁻¹ ≤ 1 := (inv_le_one₀ hKpos).2 hK
  have hnonneg : 0 ≤ 1 - K⁻¹ ^ 2 := by nlinarith
  have hsqrt := Real.sq_sqrt hnonneg
  have hsq := projectionAngle_sq hK u v h
  have hrhs : 0 ≤ Real.sqrt (1 - K⁻¹ ^ 2) * ‖u‖ * ‖v‖ := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hrhs).mp
  simpa only [mul_pow, hsqrt] using hsq

end ProofProject
