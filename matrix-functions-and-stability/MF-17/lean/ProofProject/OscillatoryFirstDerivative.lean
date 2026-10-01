import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Reciprocal variation in the first-derivative oscillatory estimate

If the derivative of a real function has a fixed sign, the variation of its
reciprocal is the absolute difference of its endpoint values. A lower bound
`δ` on the absolute value of the function therefore gives the bound `2 / δ`.
The FTC integrability hypothesis is explicit; a continuous-derivative version
supplies it automatically.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

/-- The signed reciprocal derivative has the expected exact integral. -/
theorem integral_deriv_div_sq_eq_inv_sub {a b : ℝ} (hab : a ≤ b)
    {p p' : ℝ → ℝ}
    (hp : ∀ u ∈ Icc a b, HasDerivAt p (p' u) u)
    (hne : ∀ u ∈ Icc a b, p u ≠ 0)
    (hint : IntervalIntegrable (fun u => p' u / p u ^ 2) volume a b) :
    (∫ u in a..b, p' u / p u ^ 2) = (p a)⁻¹ - (p b)⁻¹ := by
  have hd : ∀ u ∈ uIcc a b,
      HasDerivAt (fun v => (p v)⁻¹) (-(p' u / p u ^ 2)) u := by
    intro u hu
    have hu' : u ∈ Icc a b := by simpa only [uIcc_of_le hab] using hu
    simpa only [neg_div] using! (hp u hu').inv (hne u hu')
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint.neg
  rw [intervalIntegral.integral_neg] at hf
  linarith

/-- Taking the absolute reciprocal derivative preserves interval integrability. -/
theorem intervalIntegrable_abs_deriv_div_sq {a b : ℝ} {p p' : ℝ → ℝ}
    (hint : IntervalIntegrable (fun u => p' u / p u ^ 2) volume a b) :
    IntervalIntegrable (fun u => |p' u| / |p u| ^ 2) volume a b := by
  simpa only [Real.norm_eq_abs, abs_div, abs_pow] using hint.norm

/-- For either fixed sign of `p'`, the exact reciprocal variation is an endpoint
quantity. No sign assumption on `p` itself is needed. -/
theorem reciprocal_variation_eq_abs_inv_sub {a b : ℝ} (hab : a ≤ b)
    {p p' : ℝ → ℝ}
    (hp : ∀ u ∈ Icc a b, HasDerivAt p (p' u) u)
    (hne : ∀ u ∈ Icc a b, p u ≠ 0)
    (hint : IntervalIntegrable (fun u => p' u / p u ^ 2) volume a b)
    (hsign : (∀ u ∈ Icc a b, 0 ≤ p' u) ∨ (∀ u ∈ Icc a b, p' u ≤ 0)) :
    (∫ u in a..b, |p' u| / |p u| ^ 2) = |(p b)⁻¹ - (p a)⁻¹| := by
  have hftc := integral_deriv_div_sq_eq_inv_sub hab hp hne hint
  rcases hsign with hpos | hneg
  · have hnonneg : 0 ≤ ∫ u in a..b, p' u / p u ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun u hu => div_nonneg (hpos u hu) (sq_nonneg _))
    calc
      _ = ∫ u in a..b, p' u / p u ^ 2 := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : u ∈ Icc a b := by simpa only [uIcc_of_le hab] using hu
        simp only [abs_of_nonneg (hpos u hu'), sq_abs]
      _ = |∫ u in a..b, p' u / p u ^ 2| := (abs_of_nonneg hnonneg).symm
      _ = _ := by rw [hftc, abs_sub_comm]
  · have hnonneg : 0 ≤ ∫ u in a..b, -(p' u / p u ^ 2) :=
      intervalIntegral.integral_nonneg hab (fun u hu =>
        neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (hneg u hu) (sq_nonneg _)))
    rw [intervalIntegral.integral_neg] at hnonneg
    calc
      _ = ∫ u in a..b, -(p' u / p u ^ 2) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : u ∈ Icc a b := by simpa only [uIcc_of_le hab] using hu
        simp only [abs_of_nonpos (hneg u hu'), sq_abs, neg_div]
      _ = -(∫ u in a..b, p' u / p u ^ 2) := by rw [intervalIntegral.integral_neg]
      _ = |∫ u in a..b, p' u / p u ^ 2| :=
        (abs_of_nonpos (by linarith)).symm
      _ = _ := by rw [hftc, abs_sub_comm]

/-- The endpoint bound used in the first-derivative test. -/
theorem abs_inv_sub_le_two_div {u v δ : ℝ} (hδ : 0 < δ)
    (hu : δ ≤ |u|) (hv : δ ≤ |v|) : |v⁻¹ - u⁻¹| ≤ 2 / δ := by
  calc
    _ ≤ |v⁻¹| + |u⁻¹| := abs_sub _ _
    _ ≤ δ⁻¹ + δ⁻¹ := by
      rw [abs_inv, abs_inv]
      exact add_le_add ((inv_le_inv₀ (hδ.trans_le hv) hδ).mpr hv)
        ((inv_le_inv₀ (hδ.trans_le hu) hδ).mpr hu)
    _ = _ := by ring

/-- The reciprocal variation is at most `2 / δ` whenever the denominator is
bounded away from zero and the numerator has a fixed sign. -/
theorem reciprocal_variation_le_two_div {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    {p p' : ℝ → ℝ}
    (hp : ∀ u ∈ Icc a b, HasDerivAt p (p' u) u)
    (hsep : ∀ u ∈ Icc a b, δ ≤ |p u|)
    (hint : IntervalIntegrable (fun u => p' u / p u ^ 2) volume a b)
    (hsign : (∀ u ∈ Icc a b, 0 ≤ p' u) ∨ (∀ u ∈ Icc a b, p' u ≤ 0)) :
    (∫ u in a..b, |p' u| / |p u| ^ 2) ≤ 2 / δ := by
  have hne (u : ℝ) (hu : u ∈ Icc a b) : p u ≠ 0 :=
    abs_pos.mp (hδ.trans_le (hsep u hu))
  rw [reciprocal_variation_eq_abs_inv_sub hab hp hne hint hsign]
  exact abs_inv_sub_le_two_div hδ (hsep a ⟨le_rfl, hab⟩) (hsep b ⟨hab, le_rfl⟩)

/-- Continuous derivative and a nonvanishing denominator provide the explicit
FTC integrability premise. -/
theorem reciprocal_derivative_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    {p p' : ℝ → ℝ}
    (hp : ∀ u ∈ Icc a b, HasDerivAt p (p' u) u)
    (hp' : ContinuousOn p' (Icc a b))
    (hne : ∀ u ∈ Icc a b, p u ≠ 0) :
    IntervalIntegrable (fun u => p' u / p u ^ 2) volume a b := by
  have hc : ContinuousOn p (Icc a b) := fun u hu => (hp u hu).continuousAt.continuousWithinAt
  exact (hp'.div (hc.pow 2) (fun u hu => pow_ne_zero 2 (hne u hu))).intervalIntegrable_of_Icc hab

/-- The `C¹` form of the reciprocal-variation estimate for smooth phases. -/
theorem reciprocal_variation_le_two_div_of_continuousOn {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) {p p' : ℝ → ℝ}
    (hp : ∀ u ∈ Icc a b, HasDerivAt p (p' u) u)
    (hp' : ContinuousOn p' (Icc a b))
    (hsep : ∀ u ∈ Icc a b, δ ≤ |p u|)
    (hsign : (∀ u ∈ Icc a b, 0 ≤ p' u) ∨ (∀ u ∈ Icc a b, p' u ≤ 0)) :
    (∫ u in a..b, |p' u| / |p u| ^ 2) ≤ 2 / δ := by
  apply reciprocal_variation_le_two_div hab hδ hp hsep
  · exact reciprocal_derivative_intervalIntegrable hab hp hp' (fun u hu =>
      abs_pos.mp (hδ.trans_le (hsep u hu)))
  · exact hsign

end ProofProject
