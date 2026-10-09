import ProofProject.ResolventKernelIntegration
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Complex-amplitude integration by parts for a nonstationary real phase

The reciprocal phase derivative is used only on an interval where it is
nonzero. The exact endpoint terms are retained, and the remainder norm is
bounded without assuming a real amplitude.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

def oscillatoryExponential (φ : ℝ → ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((φ x : ℂ) * Complex.I)

@[simp]
theorem norm_oscillatoryExponential (φ : ℝ → ℝ) (x : ℝ) :
    ‖oscillatoryExponential φ x‖ = 1 := by
  simp [oscillatoryExponential, Complex.norm_exp]

theorem oscillatoryExponential_hasDerivAt {φ : ℝ → ℝ} {p x : ℝ}
    (hφ : HasDerivAt φ p x) :
    HasDerivAt (oscillatoryExponential φ)
      (((p : ℂ) * Complex.I) * oscillatoryExponential φ x) x := by
  unfold oscillatoryExponential
  convert (hφ.ofReal_comp.mul_const Complex.I).cexp using 1
  ring

def oscillatoryQuotient (A : ℝ → ℂ) (p : ℝ → ℝ) (x : ℝ) : ℂ :=
  A x / ((p x : ℂ) * Complex.I)

def oscillatoryRemainder (A A' : ℝ → ℂ) (p p' : ℝ → ℝ) (x : ℝ) : ℂ :=
  A' x / ((p x : ℂ) * Complex.I) -
    A x * (p' x : ℂ) / ((p x : ℂ) ^ 2 * Complex.I)

theorem oscillatoryQuotient_hasDerivAt {A A' : ℝ → ℂ} {p p' : ℝ → ℝ} {x : ℝ}
    (hA : HasDerivAt A (A' x) x) (hp : HasDerivAt p (p' x) x) (hp0 : p x ≠ 0) :
    HasDerivAt (oscillatoryQuotient A p) (oscillatoryRemainder A A' p p' x) x := by
  have hpC : (p x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp0
  convert! hA.div (hp.ofReal_comp.mul_const Complex.I) (mul_ne_zero hpC Complex.I_ne_zero) using 1
  dsimp [oscillatoryRemainder]
  field_simp [hpC]

@[simp]
theorem norm_oscillatoryQuotient (A : ℝ → ℂ) (p : ℝ → ℝ) (x : ℝ) :
    ‖oscillatoryQuotient A p x‖ = ‖A x‖ / |p x| := by
  simp [oscillatoryQuotient, Complex.norm_real, Real.norm_eq_abs]

theorem norm_oscillatoryRemainder_le (A A' : ℝ → ℂ) (p p' : ℝ → ℝ) (x : ℝ) :
    ‖oscillatoryRemainder A A' p p' x‖ ≤
      ‖A' x‖ / |p x| + ‖A x‖ * |p' x| / |p x| ^ 2 := by
  apply (norm_sub_le _ _).trans_eq
  simp [norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- The exact integration-by-parts identity with both endpoint terms. -/
theorem oscillatory_integral_integration_by_parts {a b : ℝ} (hab : a ≤ b)
    {A A' : ℝ → ℂ} {φ p p' : ℝ → ℝ}
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hp0 : ∀ x ∈ Icc a b, p x ≠ 0)
    (hA' : ContinuousOn A' (Icc a b)) (hp' : ContinuousOn p' (Icc a b)) :
    (∫ x in a..b, A x * oscillatoryExponential φ x) =
      oscillatoryQuotient A p b * oscillatoryExponential φ b -
      oscillatoryQuotient A p a * oscillatoryExponential φ a -
        ∫ x in a..b, oscillatoryRemainder A A' p p' x * oscillatoryExponential φ x := by
  have hAc : ContinuousOn A (Icc a b) := fun x hx => (hA x hx).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Icc a b) := fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hec : ContinuousOn (oscillatoryExponential φ) (Icc a b) := fun x hx =>
    (oscillatoryExponential_hasDerivAt (hφ x hx)).continuousAt.continuousWithinAt
  have hpC : ∀ x ∈ Icc a b, (p x : ℂ) ≠ 0 := fun x hx => Complex.ofReal_ne_zero.mpr (hp0 x hx)
  have hR : ContinuousOn (oscillatoryRemainder A A' p p') (Icc a b) := by
    apply ContinuousOn.sub
    · exact hA'.div ((Complex.continuous_ofReal.comp_continuousOn hpc).mul_const _)
        (fun x hx => mul_ne_zero (hpC x hx) Complex.I_ne_zero)
    · exact (hAc.mul (Complex.continuous_ofReal.comp_continuousOn hp')).div
        (((Complex.continuous_ofReal.comp_continuousOn hpc).pow 2).mul_const _)
        (fun x hx => mul_ne_zero (pow_ne_zero _ (hpC x hx)) Complex.I_ne_zero)
  have hdE : ContinuousOn (fun x => ((p x : ℂ) * Complex.I) * oscillatoryExponential φ x)
      (Icc a b) := ((Complex.continuous_ofReal.comp_continuousOn hpc).mul_const _).mul hec
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => oscillatoryQuotient_hasDerivAt
      (hA x (by simpa only [uIcc_of_le hab] using hx))
      (hp x (by simpa only [uIcc_of_le hab] using hx))
      (hp0 x (by simpa only [uIcc_of_le hab] using hx)))
    (fun x hx => oscillatoryExponential_hasDerivAt
      (hφ x (by simpa only [uIcc_of_le hab] using hx)))
    (hR.intervalIntegrable_of_Icc hab) (hdE.intervalIntegrable_of_Icc hab)
  convert h using 1
  apply intervalIntegral.integral_congr
  intro x hx
  have hpx : (p x : ℂ) * Complex.I ≠ 0 := mul_ne_zero
    (hpC x (by simpa only [uIcc_of_le hab] using hx)) Complex.I_ne_zero
  dsimp [oscillatoryQuotient]
  field_simp [hpC x (by simpa only [uIcc_of_le hab] using hx)]

/-- The norm bound retains the reciprocal-variation integral for a separate
real-variable estimate. -/
theorem norm_oscillatory_integral_le {a b : ℝ} (hab : a ≤ b)
    {A A' : ℝ → ℂ} {φ p p' : ℝ → ℝ}
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hp0 : ∀ x ∈ Icc a b, p x ≠ 0)
    (hA' : ContinuousOn A' (Icc a b)) (hp' : ContinuousOn p' (Icc a b)) :
    ‖∫ x in a..b, A x * oscillatoryExponential φ x‖ ≤
      ‖A b‖ / |p b| + ‖A a‖ / |p a| +
        ∫ x in a..b, (‖A' x‖ / |p x| + ‖A x‖ * |p' x| / |p x| ^ 2) := by
  have hAc : ContinuousOn A (Icc a b) := fun x hx => (hA x hx).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Icc a b) := fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hAbs : ∀ x ∈ Icc a b, |p x| ≠ 0 := fun x hx => abs_ne_zero.mpr (hp0 x hx)
  have hbound : ContinuousOn (fun x => ‖A' x‖ / |p x| +
      ‖A x‖ * |p' x| / |p x| ^ 2) (Icc a b) :=
    (hA'.norm.div hpc.abs hAbs).add
      ((hAc.norm.mul hp'.abs).div (hpc.abs.pow 2) (fun x hx => pow_ne_zero _ (hAbs x hx)))
  rw [oscillatory_integral_integration_by_parts hab hA hφ hp hp0 hA' hp']
  calc
    _ ≤ ‖oscillatoryQuotient A p b * oscillatoryExponential φ b‖ +
        ‖oscillatoryQuotient A p a * oscillatoryExponential φ a‖ +
        ‖∫ x in a..b, oscillatoryRemainder A A' p p' x * oscillatoryExponential φ x‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = ‖A b‖ / |p b| + ‖A a‖ / |p a| +
        ‖∫ x in a..b, oscillatoryRemainder A A' p p' x * oscillatoryExponential φ x‖ := by
      simp only [norm_mul, norm_oscillatoryExponential, mul_one, norm_oscillatoryQuotient]
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply intervalIntegral.norm_integral_le_of_norm_le hab _
        (hbound.intervalIntegrable_of_Icc hab)
      exact Filter.Eventually.of_forall fun x _ => by
        rw [norm_mul, norm_oscillatoryExponential, mul_one]
        exact norm_oscillatoryRemainder_le A A' p p' x

end ProofProject
