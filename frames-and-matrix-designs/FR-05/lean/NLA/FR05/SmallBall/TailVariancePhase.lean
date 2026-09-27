/-
Polar normalization of the tail variance profile in Lemma 3.6.

The exact expansion from `SmallBallAlgebra` has one complex correlation term.
Writing that term in polar form gives `A + B * cos (δ + φ)`.  Nonnegativity of
the variance profile at its adverse phase supplies `B ≤ A`, so the shifted
circle estimate applies under the source branch `A ≥ 1 / 4`.
-/
import NLA.FR05.SmallBall.SmallBallAlgebra
import NLA.FR05.SmallBall.PhaseAffine

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace NLA.FR05

/-- The complex correlation in the exact tail variance expansion. -/
def tailCorrelation {n : ℕ} (p q : Signal n) : ℂ := star p ⬝ᵥ q

/-- The constant term of the tail variance profile. -/
def tailVarianceConstant {n : ℕ} (p q : Signal n) : ℝ :=
  tailEnergy p + tailEnergy q

/-- The nonnegative cosine amplitude of the tail variance profile. -/
def tailVarianceAmplitude {n : ℕ} (p q : Signal n) : ℝ :=
  2 * ‖tailCorrelation p q‖

/-- A polar phase for the tail correlation. -/
def tailVariancePhase {n : ℕ} (p q : Signal n) : ℝ :=
  Complex.arg (tailCorrelation p q)

theorem tailCorrelation_polar {n : ℕ} (p q : Signal n) :
    ((‖tailCorrelation p q‖ : ℝ) : ℂ) *
        Complex.exp ((tailVariancePhase p q : ℂ) * Complex.I) =
      tailCorrelation p q := by
  unfold tailVariancePhase tailCorrelation
  exact Complex.norm_mul_exp_arg_mul_I (star p ⬝ᵥ q)

theorem tailCorrelation_phase_re {n : ℕ} (p q : Signal n) (φ : ℝ) :
    (Complex.exp ((φ : ℂ) * Complex.I) * tailCorrelation p q).re =
      ‖tailCorrelation p q‖ * Real.cos (tailVariancePhase p q + φ) := by
  have hpolar := tailCorrelation_polar p q
  have hproduct :
      Complex.exp ((φ : ℂ) * Complex.I) * tailCorrelation p q =
        ((‖tailCorrelation p q‖ : ℝ) : ℂ) *
          Complex.exp (((tailVariancePhase p q + φ : ℝ) : ℂ) * Complex.I) := by
    calc
      Complex.exp ((φ : ℂ) * Complex.I) * tailCorrelation p q =
          Complex.exp ((φ : ℂ) * Complex.I) *
            (((‖tailCorrelation p q‖ : ℝ) : ℂ) *
              Complex.exp ((tailVariancePhase p q : ℂ) * Complex.I)) := by
        rw [hpolar]
      _ = ((‖tailCorrelation p q‖ : ℝ) : ℂ) *
            Complex.exp ((tailVariancePhase p q : ℂ) * Complex.I) *
              Complex.exp ((φ : ℂ) * Complex.I) := by ring
      _ = ((‖tailCorrelation p q‖ : ℝ) : ℂ) *
            Complex.exp ((tailVariancePhase p q : ℂ) * Complex.I +
              (φ : ℂ) * Complex.I) := by
        rw [Complex.exp_add]
        ring
      _ = ((‖tailCorrelation p q‖ : ℝ) : ℂ) *
            Complex.exp (((tailVariancePhase p q + φ : ℝ) : ℂ) * Complex.I) := by
        congr 2
        push_cast
        ring
  rw [hproduct, Complex.exp_ofReal_mul_I (tailVariancePhase p q + φ)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one]

/-- The source tail variance is an affine cosine profile in the free phase. -/
theorem tailVarianceProfile_cosine_normalForm {n : ℕ}
    (p q : Signal n) (φ : ℝ) :
    tailVarianceProfile p q φ =
      tailVarianceConstant p q +
        tailVarianceAmplitude p q * Real.cos (tailVariancePhase p q + φ) := by
  rw [tailVarianceProfile_expand]
  change tailEnergy p + tailEnergy q +
      2 * (Complex.exp ((φ : ℂ) * Complex.I) * tailCorrelation p q).re =
    tailVarianceConstant p q +
      tailVarianceAmplitude p q * Real.cos (tailVariancePhase p q + φ)
  rw [tailCorrelation_phase_re]
  unfold tailVarianceConstant tailVarianceAmplitude
  ring

theorem tailVarianceAmplitude_nonneg {n : ℕ} (p q : Signal n) :
    0 ≤ tailVarianceAmplitude p q := by
  unfold tailVarianceAmplitude
  positivity

/-- Positivity of the squared norm at the adverse phase gives the sharp
amplitude domination `B ≤ A`. -/
theorem tailVarianceAmplitude_le_constant {n : ℕ} (p q : Signal n) :
    tailVarianceAmplitude p q ≤ tailVarianceConstant p q := by
  have hnonneg := tailVarianceProfile_nonneg p q
    (Real.pi - tailVariancePhase p q)
  rw [tailVarianceProfile_cosine_normalForm] at hnonneg
  have hphase : tailVariancePhase p q +
      (Real.pi - tailVariancePhase p q) = Real.pi := by ring
  rw [hphase, Real.cos_pi] at hnonneg
  linarith

theorem tailVarianceConstant_ge_quarter_of_energy {n : ℕ} (p q : Signal n)
    (henergy : (1 / 4 : ℝ) ≤ tailEnergy p + tailEnergy q) :
    (1 / 4 : ℝ) ≤ tailVarianceConstant p q := by
  simpa only [tailVarianceConstant] using henergy

/-- The variance sublevel set on the source phase interval. -/
def tailVariancePhaseSublevel {n : ℕ} (p q : Signal n) (t : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧ tailVarianceProfile p q φ ≤ t ^ 2}

theorem tailVariancePhaseSublevel_eq_shiftedAffine {n : ℕ}
    (p q : Signal n) (t : ℝ) :
    tailVariancePhaseSublevel p q t =
      shiftedAffineCosinePhaseSublevel (tailVariancePhase p q)
        (tailVarianceConstant p q) (tailVarianceAmplitude p q) t := by
  ext φ
  simp only [tailVariancePhaseSublevel, shiftedAffineCosinePhaseSublevel,
    Set.mem_ofPred_eq]
  rw [tailVarianceProfile_cosine_normalForm]

/-- In the tail-dominated branch `tailEnergy p + tailEnergy q ≥ 1/4`, a
uniform source phase makes small tail variance occur with probability at most
`4t`. -/
theorem sourceUniformInterval_tailVariancePhaseSublevel_le_four_mul_of_energy
    {n : ℕ} (p q : Signal n) (t : ℝ) (ht : 0 ≤ t)
    (henergy : (1 / 4 : ℝ) ≤ tailEnergy p + tailEnergy q) :
    sourceUniformInterval 0 (2 * Real.pi) (tailVariancePhaseSublevel p q t) ≤
      ENNReal.ofReal (4 * t) := by
  rw [tailVariancePhaseSublevel_eq_shiftedAffine]
  exact sourceUniformInterval_shiftedAffineCosinePhaseSublevel_le_four_mul_of_quarter
    (tailVariancePhase p q) (tailVarianceConstant p q) (tailVarianceAmplitude p q) t ht
    (tailVarianceConstant_ge_quarter_of_energy p q henergy)
    (tailVarianceAmplitude_nonneg p q)
    (tailVarianceAmplitude_le_constant p q)

end NLA.FR05
