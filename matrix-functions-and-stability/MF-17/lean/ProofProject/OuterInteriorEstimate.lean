import ProofProject.OuterSectorFunction
import ProofProject.AnalyticMajorant
import ProofProject.AnalyticCircleMean
import ProofProject.SectorPower

/-! The interior polynomial estimate with the exact growth exponent. -/

noncomputable section

namespace ProofProject

open Metric MeasureTheory

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

lemma outer_phase_sqrt_lt_one {K : ℝ} (hK : 1 < K) :
    Real.sqrt (1 - K⁻¹ ^ 2) < 1 := by
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hi0 : 0 < K⁻¹ := inv_pos.mpr hK0
  have hi1 : K⁻¹ < 1 := (inv_lt_one₀ hK0).mpr hK
  have hd : 0 ≤ 1 - K⁻¹ ^ 2 := by nlinarith
  have he := Real.sq_sqrt hd
  nlinarith [Real.sqrt_nonneg (1 - K⁻¹ ^ 2), sq_pos_of_pos hi0]

lemma outer_phase_constant_le {K : ℝ} (hK : 1 < K) :
    1 + Real.sqrt (1 - K⁻¹ ^ 2) ≤
      (1 - Real.sqrt (1 - K⁻¹ ^ 2)) * (4 * K ^ 2) := by
  let ρ := Real.sqrt (1 - K⁻¹ ^ 2)
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hi0 : 0 ≤ K⁻¹ := inv_nonneg.mpr hK0.le
  have hi1 : K⁻¹ ≤ 1 := (inv_le_one₀ hK0).mpr hK.le
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ < 1 := outer_phase_sqrt_lt_one hK
  have hρsq : ρ ^ 2 = 1 - K⁻¹ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hid : K ^ 2 * (1 - ρ) * (1 + ρ) = 1 := by
    calc
      _ = K ^ 2 * (1 - ρ ^ 2) := by ring
      _ = 1 := by rw [hρsq]; simp only [sub_sub_cancel, ← mul_pow,
        mul_inv_cancel₀ hK0.ne', one_pow]
  have hm := mul_nonneg (mul_nonneg (sq_nonneg K) (sub_pos.mpr hρ1).le)
    (sub_pos.mpr hρ1).le
  change 1 + ρ ≤ (1 - ρ) * (4 * K ^ 2)
  nlinarith

lemma disk_norm_le {q : ℂ} {w ρ : ℝ} (hw : 0 ≤ w)
    (he : ‖q - (w : ℂ)‖ ≤ ρ * w) : ‖q‖ ≤ (1 + ρ) * w := by
  calc
    ‖q‖ = ‖(q - (w : ℂ)) + (w : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖q - (w : ℂ)‖ + ‖(w : ℂ)‖ := norm_add_le _ _
    _ ≤ ρ * w + w := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      linarith
    _ = _ := by ring

/-- The actual finite projection hypothesis gives the source interior bound,
with a dimension-independent factor and the unmodified target exponent. -/
theorem outerPolynomial_interior_estimate {h : Polynomial ℂ} {K : ℝ}
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0)
    (hproj : HasPolynomialCircleProjectionBound h K) (hK : 1 < K)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖h.eval z‖ ^ 2 ≤ 4 * K ^ 2 *
      ((1 + ‖z‖) / (1 - ‖z‖)) ^ growthExponent K *
        ∫ w : AddCircle (1 : ℝ), ‖h.eval (fourier 1 w)‖ ^ 2 ∂AddCircle.haarAddCircle := by
  let ρ := Real.sqrt (1 - K⁻¹ ^ 2)
  let W := ∫ w : AddCircle (1 : ℝ), ‖h.eval (fourier 1 w)‖ ^ 2 ∂AddCircle.haarAddCircle
  let P := ((1 + ‖z‖) / (1 - ‖z‖)) ^ growthExponent K
  have hρ1 : ρ < 1 := outer_phase_sqrt_lt_one hK
  have hW : 0 ≤ W := integral_nonneg fun _ => sq_nonneg _
  have hP : 0 ≤ P := Real.rpow_nonneg
    (div_nonneg (by positivity) (sub_pos.mpr hz).le) _
  obtain ⟨q, r, hr, hq, hsector, hdisk⟩ := exists_outerSectorFunction hh hproj hK
  have hq1 : DifferentiableOn ℂ q (closedBall 0 1) :=
    hq.mono (closedBall_subset_closedBall hr.le)
  have hqnz (w : ℂ) (hw : ‖w‖ ≤ 1) : q w ≠ 0 := by
    intro he
    have hp := (hsector w hw).1
    simpa only [he, Complex.zero_re, lt_self_iff_false] using hp
  have hmaj : (1 - ρ) * ‖h.eval z‖ ^ 2 ≤ ‖q z‖ := by
    apply analytic_sq_norm_majorant h.differentiable.differentiableOn hq1 hqnz
      (sub_pos.mpr hρ1).le _ hz.le
    intro w hw
    exact (diskSector_re_lower (hdisk w hw)).trans (Complex.re_le_norm _)
  have hzero : ‖q 0‖ ≤ (1 + ρ) * W := by
    apply analytic_circle_norm_zero_le_of_boundary hr hq h (1 + ρ)
    intro w hw
    exact disk_norm_le (sq_nonneg _) (hdisk w hw)
  have hrad : ‖q z‖ ≤ ‖q 0‖ * P :=
    sector_growth_norm_le hK (hq1.mono ball_subset_closedBall)
      (fun w hw => (hsector w hw.le).1)
      (fun w hw => (hsector w hw.le).2) hz
  have hc : 1 + ρ ≤ (1 - ρ) * (4 * K ^ 2) := outer_phase_constant_le hK
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr hρ1)).mp
  change (1 - ρ) * ‖h.eval z‖ ^ 2 ≤ (1 - ρ) * (4 * K ^ 2 * P * W)
  calc
    _ ≤ ‖q z‖ := hmaj
    _ ≤ ‖q 0‖ * P := hrad
    _ ≤ ((1 + ρ) * W) * P := mul_le_mul_of_nonneg_right hzero hP
    _ ≤ (((1 - ρ) * (4 * K ^ 2)) * W) * P :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hW) hP
    _ = _ := by ring

end ProofProject
