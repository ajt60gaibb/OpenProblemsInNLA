import ProofProject.SourcePhaseDefs
import ProofProject.DirichletKernel

/-! Uniform radial bounds for the eventual boundary-moment passage. -/

noncomputable section

namespace ProofProject

/-- A radial chord dominates the angular distance uniformly, even at radius zero. -/
theorem source_radial_chord_lower {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hθ : |θ| ≤ Real.pi) :
    |θ| / Real.pi ≤ ‖1 - (r : ℂ) * sourceCircle θ‖ := by
  have hrnorm : ‖(r : ℂ) * sourceCircle θ‖ = r := by
    rw [norm_mul, norm_sourceCircle, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0]
  have hrad : 1 - r ≤ ‖1 - (r : ℂ) * sourceCircle θ‖ := by
    simpa only [norm_one, hrnorm] using
      norm_sub_norm_le (1 : ℂ) ((r : ℂ) * sourceCircle θ)
  have hdiff : ‖(r : ℂ) * sourceCircle θ - sourceCircle θ‖ = 1 - r := by
    rw [← sub_one_mul, norm_mul, norm_sourceCircle, mul_one,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (by linarith : r - 1 ≤ 0)]
    ring
  have ht := norm_add_le (1 - (r : ℂ) * sourceCircle θ)
    ((r : ℂ) * sourceCircle θ - sourceCircle θ)
  rw [sub_add_sub_cancel] at ht
  rw [hdiff] at ht
  have hc := norm_circle_exp_sub_one_lower hθ
  change 2 * |θ| / Real.pi ≤ ‖sourceCircle θ - 1‖ at hc
  rw [norm_sub_rev, mul_div_assoc] at hc
  linarith

/-- A uniform majorant for the square of the actual source factor on radial circles.
The angular singularity is integrable when `α < 1`; the point `θ = 0` is omitted. -/
theorem sourceWeightFactor_radial_norm_sq_le {α r θ : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hθ0 : 0 < |θ|) (hθπ : |θ| ≤ Real.pi) :
    ‖sourceWeightFactor α ((r : ℂ) * sourceCircle θ)‖ ^ 2 ≤
      (Real.exp (2 * sourceWeightCorrectionBound α) * (2 : ℝ) ^ α *
        Real.pi ^ α) * |θ| ^ (-α) := by
  have hz : ‖(r : ℂ) * sourceCircle θ‖ ≤ 1 := by
    simpa [norm_mul, norm_sourceCircle, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0] using hr1
  have hweight := (sourceWeightFactor_norm_sq_bounds hα0 hα1 hz).2
  have hnum : ‖1 + (r : ℂ) * sourceCircle θ‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) ((r : ℂ) * sourceCircle θ)
    rw [norm_one] at h
    linarith
  have hden := source_radial_chord_lower hr0 hr1 hθπ
  have ht : 0 < |θ| / Real.pi := div_pos hθ0 Real.pi_pos
  have hd : 0 < ‖1 - (r : ℂ) * sourceCircle θ‖ := ht.trans_le hden
  have hratio :
      ‖1 + (r : ℂ) * sourceCircle θ‖ ^ α /
          ‖1 - (r : ℂ) * sourceCircle θ‖ ^ α ≤
        (2 : ℝ) ^ α / (|θ| / Real.pi) ^ α := by
    exact div_le_div₀ (by positivity)
      (Real.rpow_le_rpow (norm_nonneg _) hnum hα0.le)
      (Real.rpow_pos_of_pos ht _)
      (Real.rpow_le_rpow ht.le hden hα0.le)
  calc
    _ ≤ Real.exp (2 * sourceWeightCorrectionBound α) *
        ((2 : ℝ) ^ α / (|θ| / Real.pi) ^ α) :=
      hweight.trans (mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le)
    _ = _ := by
      rw [Real.div_rpow (abs_nonneg _) Real.pi_pos.le, Real.rpow_neg (abs_nonneg _)]
      field_simp

end ProofProject
