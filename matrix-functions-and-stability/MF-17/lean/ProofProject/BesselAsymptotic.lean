import ProofProject.BesselOscillator
import ProofProject.OscillatorAsymptotic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The actual Bessel kernel has a two-phase integrable remainder

The oscillator equation supplies real sine/cosine coefficients. The change
of variable `r = 2 sqrt u` converts its `O(1/r)` error into `O(u^(-5/4))`.
The leading coefficients are allowed to vanish; their exact numerical values
are unnecessary for the operator estimate.
-/

noncomputable section

namespace ProofProject

private theorem two_sqrt_rpow {u : ℝ} (hu : 0 < u) (p : ℝ) :
    (2 * Real.sqrt u) ^ p = (2 : ℝ) ^ p * u ^ (p / 2) := by
  rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hu.le]
  congr 2
  ring

/-- Undo the oscillator substitution, with the normalization retained exactly. -/
theorem besselKernel_eq_oscillator {u : ℝ} (hu : 0 < u) :
    besselKernel u = (2 * (2 : ℝ) ^ (-3 / 2 : ℝ)) * u ^ (-3 / 4 : ℝ) *
      besselOscillator (2 * Real.sqrt u) := by
  have hr : 0 < 2 * Real.sqrt u := by positivity
  have harg : (2 * Real.sqrt u) ^ 2 / 4 = u := by
    nlinarith [Real.sq_sqrt hu.le]
  have hp₂ : (2 : ℝ) ^ (-3 / 2 : ℝ) * 2 ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hpu : u ^ (-3 / 4 : ℝ) * u ^ (3 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hu]
    norm_num
  rw [besselOscillator_eq_rpow hr, harg, two_sqrt_rpow hu]
  norm_num only [show (3 / 2 : ℝ) / 2 = 3 / 4 by norm_num]
  calc
    _ = ((2 : ℝ) ^ (-3 / 2 : ℝ) * 2 ^ (3 / 2 : ℝ)) *
        (u ^ (-3 / 4 : ℝ) * u ^ (3 / 4 : ℝ)) * besselKernel u := by
      rw [hp₂, hpu]
      ring
    _ = _ := by ring

/-- Real form of the asymptotic, obtained from the actual oscillator system. -/
theorem exists_besselKernel_trig_asymptotic :
    ∃ a₀ a₁ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 1 ≤ u →
      |besselKernel u - u ^ (-3 / 4 : ℝ) *
        (a₀ * Real.cos (2 * Real.sqrt u) + a₁ * Real.sin (2 * Real.sqrt u))| ≤
          C * u ^ (-5 / 4 : ℝ) := by
  obtain ⟨A₀, A₁, C₀, hC₀, hA⟩ := exists_oscillator_asymptotic
    (fun r hr => besselOscillator_hasDerivAt (by linarith : 0 < r))
    (fun r hr => besselOscillatorSlope_hasDerivAt (by linarith : 0 < r))
  let s : ℝ := 2 * (2 : ℝ) ^ (-3 / 2 : ℝ)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  refine ⟨s * A₀, s * A₁, s * C₀ / 2, by positivity, ?_⟩
  intro u hu
  have hu0 : 0 < u := by linarith
  have hsu : 1 ≤ Real.sqrt u := by
    nlinarith [Real.sq_sqrt hu0.le, Real.sqrt_nonneg u]
  have hr : 1 ≤ 2 * Real.sqrt u := by linarith
  have hextract := besselKernel_eq_oscillator hu0
  change besselKernel u = s * u ^ (-3 / 4 : ℝ) * besselOscillator (2 * Real.sqrt u)
    at hextract
  have heq : besselKernel u - u ^ (-3 / 4 : ℝ) *
      (s * A₀ * Real.cos (2 * Real.sqrt u) + s * A₁ * Real.sin (2 * Real.sqrt u)) =
      (s * u ^ (-3 / 4 : ℝ)) * (besselOscillator (2 * Real.sqrt u) -
        (A₀ * Real.cos (2 * Real.sqrt u) + A₁ * Real.sin (2 * Real.sqrt u))) := by
    rw [hextract]
    ring
  have hpower : u ^ (-3 / 4 : ℝ) / Real.sqrt u = u ^ (-5 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hu0]
    norm_num
  rw [heq, abs_mul, abs_of_nonneg (mul_nonneg hs (Real.rpow_nonneg hu0.le _))]
  calc
    _ ≤ (s * u ^ (-3 / 4 : ℝ)) * (C₀ / (2 * Real.sqrt u)) :=
      mul_le_mul_of_nonneg_left (hA _ hr) (by positivity)
    _ = (s * C₀ / 2) * (u ^ (-3 / 4 : ℝ) / Real.sqrt u) := by ring
    _ = _ := by rw [hpower]

private theorem complex_two_phase_eq (a₀ a₁ r : ℝ) :
    (((a₀ : ℂ) - Complex.I * (a₁ : ℂ)) / 2) * Complex.exp ((r : ℂ) * Complex.I) +
      (((a₀ : ℂ) + Complex.I * (a₁ : ℂ)) / 2) *
        Complex.exp (((-r : ℝ) : ℂ) * Complex.I) =
      ((a₀ * Real.cos r + a₁ * Real.sin r : ℝ) : ℂ) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg]
  calc
    _ = (a₀ : ℂ) * (Real.cos r : ℂ) -
        Complex.I ^ 2 * (a₁ : ℂ) * (Real.sin r : ℂ) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- Complex two-phase asymptotic for the factorial-series kernel itself.
The constants are fixed before the positive variable `u`. -/
theorem exists_besselKernel_asymptotic :
    ∃ cPlus cMinus : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 1 ≤ u →
      ‖(besselKernel u : ℂ) - ((u ^ (-3 / 4 : ℝ) : ℝ) : ℂ) *
        (cPlus * Complex.exp (((2 * Real.sqrt u : ℝ) : ℂ) * Complex.I) +
          cMinus * Complex.exp (((-(2 * Real.sqrt u) : ℝ) : ℂ) * Complex.I))‖ ≤
            C * u ^ (-5 / 4 : ℝ) := by
  obtain ⟨a₀, a₁, C, hC, hA⟩ := exists_besselKernel_trig_asymptotic
  refine ⟨((a₀ : ℂ) - Complex.I * (a₁ : ℂ)) / 2,
    ((a₀ : ℂ) + Complex.I * (a₁ : ℂ)) / 2, C, hC, ?_⟩
  intro u hu
  rw [complex_two_phase_eq, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact hA u hu

end ProofProject
