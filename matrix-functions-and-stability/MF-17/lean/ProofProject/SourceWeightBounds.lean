import ProofProject.SourceWeightFactor

/-!
# Quantitative norm comparison for the actual source weight

The correction exponent is uniformly bounded on the closed unit disk. The
resulting estimates compare the exact source factor to the Cayley power, and
hence to the ratio of distances from the two exceptional boundary points.
The displayed algebraic inequalities also hold at the endpoints under Lean's
totalized division; applications to analytic boundary values omit those points.
-/

noncomputable section

namespace ProofProject

/-- The inward correction exponent in the exact source formula. -/
def sourceWeightCorrection (α : ℝ) (z : ℂ) : ℂ :=
  ((α / 4 : ℝ) : ℂ) *
    ((1 - z) ^ ((sourceWeightNu α : ℝ) : ℂ) -
      (1 + z) ^ ((sourceWeightNu α : ℝ) : ℂ))

/-- A uniform absolute bound for the correction exponent on the closed disk. -/
def sourceWeightCorrectionBound (α : ℝ) : ℝ :=
  2 * (α / 4) * (2 : ℝ) ^ sourceWeightNu α

lemma sourceWeightCorrectionBound_pos {α : ℝ} (hα : 0 < α) :
    0 < sourceWeightCorrectionBound α := by
  unfold sourceWeightCorrectionBound
  positivity

lemma sourceWeightFactor_norm (α : ℝ) (z : ℂ) :
    ‖sourceWeightFactor α z‖ =
      ‖sourceCayley z‖ ^ (α / 2) * Real.exp (sourceWeightCorrection α z).re := by
  rw [sourceWeightFactor, norm_mul, Complex.norm_cpow_real, Complex.norm_exp]
  rfl

/-- Both complex powers in the correction have norm bounded by `2^ν`. -/
lemma norm_sourceWeightCorrection_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖sourceWeightCorrection α z‖ ≤ sourceWeightCorrectionBound α := by
  have hminus : ‖1 - z‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) z
    rw [norm_one] at h
    linarith
  have hplus : ‖1 + z‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) z
    rw [norm_one] at h
    linarith
  have hν := (sourceWeightNu_pos hα1).le
  have hm : ‖(1 - z) ^ ((sourceWeightNu α : ℝ) : ℂ)‖ ≤ (2 : ℝ) ^ sourceWeightNu α := by
    rw [Complex.norm_cpow_real]
    exact Real.rpow_le_rpow (norm_nonneg _) hminus hν
  have hp : ‖(1 + z) ^ ((sourceWeightNu α : ℝ) : ℂ)‖ ≤ (2 : ℝ) ^ sourceWeightNu α := by
    rw [Complex.norm_cpow_real]
    exact Real.rpow_le_rpow (norm_nonneg _) hplus hν
  rw [sourceWeightCorrection, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < α / 4)]
  calc
    _ ≤ (α / 4) *
        (‖(1 - z) ^ ((sourceWeightNu α : ℝ) : ℂ)‖ +
          ‖(1 + z) ^ ((sourceWeightNu α : ℝ) : ℂ)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ (α / 4) * ((2 : ℝ) ^ sourceWeightNu α + (2 : ℝ) ^ sourceWeightNu α) :=
      mul_le_mul_of_nonneg_left (add_le_add hm hp) (by positivity)
    _ = sourceWeightCorrectionBound α := by unfold sourceWeightCorrectionBound; ring

lemma abs_re_sourceWeightCorrection_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    |(sourceWeightCorrection α z).re| ≤ sourceWeightCorrectionBound α :=
  (Complex.abs_re_le_norm _).trans (norm_sourceWeightCorrection_le hα0 hα1 hz)

/-- The actual source factor is uniformly comparable to its Cayley power. -/
theorem sourceWeightFactor_norm_bounds {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Real.exp (-sourceWeightCorrectionBound α) * ‖sourceCayley z‖ ^ (α / 2) ≤
        ‖sourceWeightFactor α z‖ ∧
      ‖sourceWeightFactor α z‖ ≤
        Real.exp (sourceWeightCorrectionBound α) * ‖sourceCayley z‖ ^ (α / 2) := by
  have hr := abs_le.mp (abs_re_sourceWeightCorrection_le hα0 hα1 hz)
  rw [sourceWeightFactor_norm]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hr.1) (Real.rpow_nonneg (norm_nonneg _) _)
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hr.2) (Real.rpow_nonneg (norm_nonneg _) _)

/-- Squaring a half-exponent Cayley norm gives the source's exponent α. -/
lemma sourceCayley_rpow_half_sq (α : ℝ) (z : ℂ) :
    (‖sourceCayley z‖ ^ (α / 2)) ^ 2 = ‖sourceCayley z‖ ^ α := by
  rw [← Real.rpow_mul_natCast (norm_nonneg _)]
  congr 1
  norm_num

/-- Quantitative source weight order, with all constants displayed. -/
theorem sourceWeightFactor_norm_sq_bounds {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Real.exp (-2 * sourceWeightCorrectionBound α) *
        (‖1 + z‖ ^ α / ‖1 - z‖ ^ α) ≤ ‖sourceWeightFactor α z‖ ^ 2 ∧
      ‖sourceWeightFactor α z‖ ^ 2 ≤
        Real.exp (2 * sourceWeightCorrectionBound α) * (‖1 + z‖ ^ α / ‖1 - z‖ ^ α) := by
  have h := sourceWeightFactor_norm_bounds hα0 hα1 hz
  have hl := pow_le_pow_left₀ (by positivity :
      0 ≤ Real.exp (-sourceWeightCorrectionBound α) * ‖sourceCayley z‖ ^ (α / 2)) h.1 2
  have hu := pow_le_pow_left₀ (norm_nonneg _) h.2 2
  have hc : ‖sourceCayley z‖ ^ α = ‖1 + z‖ ^ α / ‖1 - z‖ ^ α := by
    rw [sourceCayley, norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [mul_pow, sourceCayley_rpow_half_sq, ← Real.exp_nat_mul, hc] at hl hu
  constructor
  · simpa only [Nat.cast_ofNat, mul_neg, neg_mul] using hl
  · simpa only [Nat.cast_ofNat] using hu

end ProofProject
