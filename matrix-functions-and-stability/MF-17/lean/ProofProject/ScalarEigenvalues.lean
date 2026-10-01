import Mathlib

/-!
# Scalar estimates for the separated diagonal lower construction

The generator eigenvalues are reciprocals of `-1 + iy`. Shifting them left
before taking reciprocals produces a controlled perturbation, and complex
exponentiation is a contraction on the closed left half-plane.
-/

noncomputable section

namespace ProofProject

/-- The desired inverse eigenvalue, whose real part is fixed at `-1`. -/
def scalarMu (y : ℝ) : ℂ := -1 + Complex.I * (y : ℂ)

/-- The corresponding generator eigenvalue. -/
def scalarLambda (y : ℝ) : ℂ := (scalarMu y)⁻¹

@[simp] theorem scalarMu_re (y : ℝ) : (scalarMu y).re = -1 := by
  simp [scalarMu]

@[simp] theorem scalarMu_im (y : ℝ) : (scalarMu y).im = y := by
  simp [scalarMu]

theorem scalarMu_ne_zero (y : ℝ) : scalarMu y ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem scalarMu_normSq (y : ℝ) : Complex.normSq (scalarMu y) = 1 + y ^ 2 := by
  simp [Complex.normSq_apply, pow_two]

theorem scalarLambda_re (y : ℝ) : (scalarLambda y).re = -1 / (1 + y ^ 2) := by
  simp [scalarLambda, Complex.inv_re, scalarMu_normSq]

theorem scalarLambda_re_neg (y : ℝ) : (scalarLambda y).re < 0 := by
  rw [scalarLambda_re]
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem scalarLambda_norm_le {y : ℝ} (hy : 0 < y) : ‖scalarLambda y‖ ≤ 1 / y := by
  have hm : y ≤ ‖scalarMu y‖ := by
    have h := Complex.abs_im_le_norm (scalarMu y)
    simpa [abs_of_pos hy] using h
  rw [scalarLambda, norm_inv, one_div]
  exact (inv_le_inv₀ (lt_of_lt_of_le hy hm) hy).2 hm

/-- The denominator in the inverse perturbation stays at least one from zero. -/
theorem scalarMu_shift_denominator_norm (y ω : ℝ) (hω : 0 ≤ ω) :
    1 ≤ ‖1 - (ω : ℂ) * scalarMu y‖ := by
  have h := Complex.abs_re_le_norm (1 - (ω : ℂ) * scalarMu y)
  have hre : (1 - (ω : ℂ) * scalarMu y).re = 1 + ω := by simp
  rw [hre, abs_of_nonneg (by positivity)] at h
  linarith

theorem scalarMu_shift_denominator_ne_zero (y ω : ℝ) (hω : 0 ≤ ω) :
    1 - (ω : ℂ) * scalarMu y ≠ 0 := by
  have h := scalarMu_shift_denominator_norm y ω hω
  intro hz
  simp only [hz, norm_zero] at h
  norm_num at h

theorem scalarLambda_sub_ne_zero (y ω : ℝ) (hω : 0 ≤ ω) :
    scalarLambda y - (ω : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
  have hneg := scalarLambda_re_neg y
  linarith

/-- Exact inverse perturbation formula, prior to taking norms. -/
theorem scalarLambda_shift_inverse_sub (y ω : ℝ) (hω : 0 ≤ ω) :
    (scalarLambda y - (ω : ℂ))⁻¹ - scalarMu y =
      (ω : ℂ) * (scalarMu y) ^ 2 / (1 - (ω : ℂ) * scalarMu y) := by
  have hμ := scalarMu_ne_zero y
  have hd := scalarMu_shift_denominator_ne_zero y ω hω
  have hlam := scalarLambda_sub_ne_zero y ω hω
  dsimp [scalarLambda] at hlam ⊢
  have hdm : 1 - scalarMu y * (ω : ℂ) ≠ 0 := by simpa [mul_comm] using hd
  field_simp [hμ, hd, hlam]
  ring_nf

/-- The source error bound, with the individual frequency rather than its maximum. -/
theorem scalarLambda_shift_inverse_error (y ω : ℝ) (hω : 0 ≤ ω) :
    ‖(scalarLambda y - (ω : ℂ))⁻¹ - scalarMu y‖ ≤ ω * (1 + y ^ 2) := by
  rw [scalarLambda_shift_inverse_sub y ω hω, norm_div, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hω,
    ← Complex.normSq_eq_norm_sq, scalarMu_normSq]
  exact div_le_self (by positivity) (scalarMu_shift_denominator_norm y ω hω)

theorem scalarLambda_shift_inverse_re_nonpos (y ω : ℝ) (hω : 0 ≤ ω) :
    ((scalarLambda y - (ω : ℂ))⁻¹).re ≤ 0 := by
  rw [Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
  exact div_nonpos_of_nonpos_of_nonneg (by have := scalarLambda_re_neg y; linarith)
    (Complex.normSq_nonneg _)

/-- Exponentiation is `1`-Lipschitz on the closed left half-plane. -/
theorem norm_exp_sub_le_of_re_nonpos {z w : ℂ} (hz : z.re ≤ 0) (hw : w.re ≤ 0) :
    ‖Complex.exp z - Complex.exp w‖ ≤ ‖z - w‖ := by
  have hc : Convex ℝ {z : ℂ | z.re ≤ 0} := by
    intro x hx y hy a b ha hb hab
    change (a • x + b • y).re ≤ 0
    simp only [Complex.add_re, Complex.smul_re]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
      (mul_nonpos_of_nonneg_of_nonpos hb hy)
  have h := hc.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Complex.exp) (f' := Complex.exp) (C := 1)
    (fun z _ => (Complex.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z hz => by simpa [Complex.norm_exp] using Real.exp_le_one_iff.mpr hz)
    hw hz
  simpa using h

/-- Inverse exponents at a nonnegative time inherit the scalar perturbation bound. -/
theorem scalarLambda_shift_exp_error (y ω t : ℝ) (hω : 0 ≤ ω) (ht : 0 ≤ t) :
    ‖Complex.exp ((t : ℂ) * (scalarLambda y - (ω : ℂ))⁻¹) -
      Complex.exp ((t : ℂ) * scalarMu y)‖ ≤ t * ω * (1 + y ^ 2) := by
  have hz : ((t : ℂ) * (scalarLambda y - (ω : ℂ))⁻¹).re ≤ 0 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos ht (scalarLambda_shift_inverse_re_nonpos y ω hω)
  have hw : ((t : ℂ) * scalarMu y).re ≤ 0 := by simpa using neg_nonpos.mpr ht
  calc
    _ ≤ ‖(t : ℂ) * (scalarLambda y - (ω : ℂ))⁻¹ - (t : ℂ) * scalarMu y‖ :=
      norm_exp_sub_le_of_re_nonpos hz hw
    _ = t * ‖(scalarLambda y - (ω : ℂ))⁻¹ - scalarMu y‖ := by
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    _ ≤ t * (ω * (1 + y ^ 2)) :=
      mul_le_mul_of_nonneg_left (scalarLambda_shift_inverse_error y ω hω) ht
    _ = _ := by ring

/-- Integer frequencies prescribe exactly the desired signs at time `π`. -/
theorem scalarMu_exp_pi (n : ℕ) :
    Complex.exp ((Real.pi : ℂ) * scalarMu n) =
      (Real.exp (-Real.pi) : ℂ) * (-1 : ℂ) ^ n := by
  have harg : (Real.pi : ℂ) * scalarMu n =
      (-Real.pi : ℂ) + (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    simp only [scalarMu, Complex.ofReal_natCast]
    ring
  rw [harg, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  simp

/-- The exact scalar decay used for entries before the transition coordinate. -/
theorem scalarLambda_exp_norm (y s : ℝ) :
    ‖Complex.exp ((s : ℂ) * scalarLambda y)‖ =
      Real.exp (-s / (1 + y ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, scalarLambda_re]
  ring

/-- Entries after the transition coordinate stay close to the identity. -/
theorem scalarLambda_exp_sub_one_norm_le {y s : ℝ} (hy : 0 < y) (hs : 0 ≤ s) :
    ‖Complex.exp ((s : ℂ) * scalarLambda y) - 1‖ ≤ s / y := by
  have hz : ((s : ℂ) * scalarLambda y).re ≤ 0 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hs (scalarLambda_re_neg y).le
  calc
    _ ≤ ‖(s : ℂ) * scalarLambda y‖ := by
      simpa using norm_exp_sub_le_of_re_nonpos hz (by simp : (0 : ℂ).re ≤ 0)
    _ = s * ‖scalarLambda y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
    _ ≤ s * (1 / y) := mul_le_mul_of_nonneg_left (scalarLambda_norm_le hy) hs
    _ = _ := by ring

/-- The sign approximation for each coordinate in the source construction. -/
theorem scalarLambda_shift_exp_pi_error (n : ℕ) (ω : ℝ) (hω : 0 ≤ ω) :
    ‖Complex.exp ((Real.pi : ℂ) * (scalarLambda n - (ω : ℂ))⁻¹) -
      (Real.exp (-Real.pi) : ℂ) * (-1 : ℂ) ^ n‖ ≤
      Real.pi * ω * (1 + (n : ℝ) ^ 2) := by
  rw [← scalarMu_exp_pi]
  exact scalarLambda_shift_exp_error n ω Real.pi hω Real.pi_pos.le

end ProofProject
