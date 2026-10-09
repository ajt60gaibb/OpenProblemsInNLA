import ProofProject.OscillatoryIntegration
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Two integrations by parts away from stationary points

The complex amplitude and its first derivative vanish at both endpoints.
The phase derivative is nonzero on the interval. Two actual integrations by
parts then leave four explicit terms, with coefficients `1, 3, 1, 3`.
No sign restriction on the amplitude or phase derivative is imposed.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

/-- The quotient used in the second integration by parts, with `i² = -1`
already simplified. -/
def oscillatorySecondQuotient (A A' : ℝ → ℂ) (p p' : ℝ → ℝ) (x : ℝ) : ℂ :=
  -A' x / (p x : ℂ) ^ 2 + A x * (p' x : ℂ) / (p x : ℂ) ^ 3

/-- The exact twice-integrated amplitude. -/
def oscillatorySecondRemainder (A A' A'' : ℝ → ℂ)
    (p p' p'' : ℝ → ℝ) (x : ℝ) : ℂ :=
  -A'' x / (p x : ℂ) ^ 2 +
    3 * A' x * (p' x : ℂ) / (p x : ℂ) ^ 3 +
    A x * (p'' x : ℂ) / (p x : ℂ) ^ 3 -
    3 * A x * (p' x : ℂ) ^ 2 / (p x : ℂ) ^ 4

theorem oscillatorySecondQuotient_mul_phaseDeriv (A A' : ℝ → ℂ)
    (p p' : ℝ → ℝ) {x : ℝ} (hp0 : p x ≠ 0) :
    oscillatorySecondQuotient A A' p p' x * ((p x : ℂ) * Complex.I) =
      oscillatoryRemainder A A' p p' x := by
  have hpC : (p x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp0
  unfold oscillatorySecondQuotient oscillatoryRemainder
  field_simp [hpC]
  simp [Complex.I_sq]
  ring

theorem oscillatorySecondQuotient_hasDerivAt
    {A A' A'' : ℝ → ℂ} {p p' p'' : ℝ → ℝ} {x : ℝ}
    (hA : HasDerivAt A (A' x) x) (hA' : HasDerivAt A' (A'' x) x)
    (hp : HasDerivAt p (p' x) x) (hp' : HasDerivAt p' (p'' x) x)
    (hp0 : p x ≠ 0) :
    HasDerivAt (oscillatorySecondQuotient A A' p p')
      (oscillatorySecondRemainder A A' A'' p p' p'' x) x := by
  have hpC : (p x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp0
  convert! ((hA'.neg.div (hp.ofReal_comp.pow 2) (pow_ne_zero 2 hpC)).add
    ((hA.mul hp'.ofReal_comp).div (hp.ofReal_comp.pow 3) (pow_ne_zero 3 hpC))) using 1
  dsimp [oscillatorySecondRemainder]
  field_simp [hpC]
  ring

theorem norm_oscillatorySecondRemainder_le (A A' A'' : ℝ → ℂ)
    (p p' p'' : ℝ → ℝ) (x : ℝ) :
    ‖oscillatorySecondRemainder A A' A'' p p' p'' x‖ ≤
      ‖A'' x‖ / |p x| ^ 2 + 3 * ‖A' x‖ * |p' x| / |p x| ^ 3 +
        ‖A x‖ * |p'' x| / |p x| ^ 3 +
        3 * ‖A x‖ * |p' x| ^ 2 / |p x| ^ 4 := by
  unfold oscillatorySecondRemainder
  refine ((norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)).trans_eq ?_
  simp [norm_pow, Complex.norm_real, Real.norm_eq_abs]

private theorem oscillatorySecondRemainder_continuousOn {a b : ℝ}
    {A A' A'' : ℝ → ℂ} {p p' p'' : ℝ → ℝ}
    (hAc : ContinuousOn A (Icc a b)) (hA'c : ContinuousOn A' (Icc a b))
    (hA''c : ContinuousOn A'' (Icc a b))
    (hpc : ContinuousOn p (Icc a b)) (hp'c : ContinuousOn p' (Icc a b))
    (hp''c : ContinuousOn p'' (Icc a b)) (hp0 : ∀ x ∈ Icc a b, p x ≠ 0) :
    ContinuousOn (oscillatorySecondRemainder A A' A'' p p' p'') (Icc a b) := by
  have hc := Complex.continuous_ofReal.comp_continuousOn hpc
  have hc' := Complex.continuous_ofReal.comp_continuousOn hp'c
  have hc'' := Complex.continuous_ofReal.comp_continuousOn hp''c
  have hne (k : ℕ) (x : ℝ) (hx : x ∈ Icc a b) : (p x : ℂ) ^ k ≠ 0 :=
    pow_ne_zero k (Complex.ofReal_ne_zero.mpr (hp0 x hx))
  exact (((hA''c.neg.div (hc.pow 2) (hne 2)).add
    (((hA'c.const_mul 3).mul hc').div (hc.pow 3) (hne 3))).add
      ((hAc.mul hc'').div (hc.pow 3) (hne 3))).sub
        (((hAc.const_mul 3).mul (hc'.pow 2)).div (hc.pow 4) (hne 4))

/-- With both amplitude boundary terms zero, two integrations by parts give
the exact four-term remainder. -/
theorem oscillatory_integral_twice_integration_by_parts {a b : ℝ} (hab : a ≤ b)
    {A A' A'' : ℝ → ℂ} {φ p p' p'' : ℝ → ℝ}
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hA' : ∀ x ∈ Icc a b, HasDerivAt A' (A'' x) x)
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hp' : ∀ x ∈ Icc a b, HasDerivAt p' (p'' x) x)
    (hp0 : ∀ x ∈ Icc a b, p x ≠ 0)
    (hA''c : ContinuousOn A'' (Icc a b)) (hp''c : ContinuousOn p'' (Icc a b))
    (ha : A a = 0) (hb : A b = 0) (ha' : A' a = 0) (hb' : A' b = 0) :
    (∫ x in a..b, A x * oscillatoryExponential φ x) =
      ∫ x in a..b, oscillatorySecondRemainder A A' A'' p p' p'' x *
        oscillatoryExponential φ x := by
  have hAc : ContinuousOn A (Icc a b) := fun x hx => (hA x hx).continuousAt.continuousWithinAt
  have hA'c : ContinuousOn A' (Icc a b) := fun x hx => (hA' x hx).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Icc a b) := fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hp'c : ContinuousOn p' (Icc a b) := fun x hx => (hp' x hx).continuousAt.continuousWithinAt
  have hSc := oscillatorySecondRemainder_continuousOn hAc hA'c hA''c hpc hp'c hp''c hp0
  have hec : ContinuousOn (oscillatoryExponential φ) (Icc a b) := fun x hx =>
    (oscillatoryExponential_hasDerivAt (hφ x hx)).continuousAt.continuousWithinAt
  have hdE : ContinuousOn (fun x => ((p x : ℂ) * Complex.I) * oscillatoryExponential φ x)
      (Icc a b) := ((Complex.continuous_ofReal.comp_continuousOn hpc).mul_const _).mul hec
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => oscillatorySecondQuotient_hasDerivAt
      (hA x (by simpa only [uIcc_of_le hab] using hx))
      (hA' x (by simpa only [uIcc_of_le hab] using hx))
      (hp x (by simpa only [uIcc_of_le hab] using hx))
      (hp' x (by simpa only [uIcc_of_le hab] using hx))
      (hp0 x (by simpa only [uIcc_of_le hab] using hx)))
    (fun x hx => oscillatoryExponential_hasDerivAt
      (hφ x (by simpa only [uIcc_of_le hab] using hx)))
    (hSc.intervalIntegrable_of_Icc hab) (hdE.intervalIntegrable_of_Icc hab)
  have hleft : (∫ x in a..b, oscillatorySecondQuotient A A' p p' x *
      (((p x : ℂ) * Complex.I) * oscillatoryExponential φ x)) =
      ∫ x in a..b, oscillatoryRemainder A A' p p' x * oscillatoryExponential φ x := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [← mul_assoc, oscillatorySecondQuotient_mul_phaseDeriv A A' p p'
      (hp0 x (by simpa only [uIcc_of_le hab] using hx))]
  rw [hleft] at hsecond
  have hfirst := oscillatory_integral_integration_by_parts hab hA hφ hp hp0 hA'c hp'c
  simp only [oscillatoryQuotient, ha, hb, zero_div, zero_mul, sub_self, zero_sub] at hfirst
  simp only [oscillatorySecondQuotient, ha, hb, ha', hb', neg_zero, zero_div,
    zero_mul, zero_add, sub_self, zero_sub] at hsecond
  rw [hfirst, hsecond, neg_neg]

/-- The concrete twice-IBP estimate, retaining the four source frequency-tail
terms and their exact coefficients. -/
theorem norm_oscillatory_integral_le_twice_integration_by_parts {a b : ℝ} (hab : a ≤ b)
    {A A' A'' : ℝ → ℂ} {φ p p' p'' : ℝ → ℝ}
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hA' : ∀ x ∈ Icc a b, HasDerivAt A' (A'' x) x)
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hp' : ∀ x ∈ Icc a b, HasDerivAt p' (p'' x) x)
    (hp0 : ∀ x ∈ Icc a b, p x ≠ 0)
    (hA''c : ContinuousOn A'' (Icc a b)) (hp''c : ContinuousOn p'' (Icc a b))
    (ha : A a = 0) (hb : A b = 0) (ha' : A' a = 0) (hb' : A' b = 0) :
    ‖∫ x in a..b, A x * oscillatoryExponential φ x‖ ≤
      ∫ x in a..b, (‖A'' x‖ / |p x| ^ 2 + 3 * ‖A' x‖ * |p' x| / |p x| ^ 3 +
        ‖A x‖ * |p'' x| / |p x| ^ 3 + 3 * ‖A x‖ * |p' x| ^ 2 / |p x| ^ 4) := by
  have hAc : ContinuousOn A (Icc a b) := fun x hx => (hA x hx).continuousAt.continuousWithinAt
  have hA'c : ContinuousOn A' (Icc a b) := fun x hx => (hA' x hx).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Icc a b) := fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hp'c : ContinuousOn p' (Icc a b) := fun x hx => (hp' x hx).continuousAt.continuousWithinAt
  have hne (k : ℕ) (x : ℝ) (hx : x ∈ Icc a b) : |p x| ^ k ≠ 0 :=
    pow_ne_zero k (abs_ne_zero.mpr (hp0 x hx))
  have hbound : ContinuousOn (fun x =>
      ‖A'' x‖ / |p x| ^ 2 + 3 * ‖A' x‖ * |p' x| / |p x| ^ 3 +
      ‖A x‖ * |p'' x| / |p x| ^ 3 + 3 * ‖A x‖ * |p' x| ^ 2 / |p x| ^ 4)
      (Icc a b) :=
    (((hA''c.norm.div (hpc.abs.pow 2) (hne 2)).add
      (((hA'c.norm.const_mul 3).mul hp'c.abs).div (hpc.abs.pow 3) (hne 3))).add
        ((hAc.norm.mul hp''c.abs).div (hpc.abs.pow 3) (hne 3))).add
          (((hAc.norm.const_mul 3).mul (hp'c.abs.pow 2)).div (hpc.abs.pow 4) (hne 4))
  rw [oscillatory_integral_twice_integration_by_parts hab hA hA' hφ hp hp' hp0
    hA''c hp''c ha hb ha' hb']
  apply intervalIntegral.norm_integral_le_of_norm_le hab _
    (hbound.intervalIntegrable_of_Icc hab)
  exact Filter.Eventually.of_forall fun x _ => by
    rw [norm_mul, norm_oscillatoryExponential, mul_one]
    exact norm_oscillatorySecondRemainder_le A A' A'' p p' p'' x

/-- Uniform amplitude and phase bounds turn the twice-IBP estimate into the
interval length times an explicit frequency-tail bound. -/
theorem norm_oscillatory_integral_le_twice_sup
    {a b δ C0 C1 C2 P1 P2 : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2)
    {A A' A'' : ℝ → ℂ} {φ p p' p'' : ℝ → ℝ}
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hA' : ∀ x ∈ Icc a b, HasDerivAt A' (A'' x) x)
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hp' : ∀ x ∈ Icc a b, HasDerivAt p' (p'' x) x)
    (hA''c : ContinuousOn A'' (Icc a b)) (hp''c : ContinuousOn p'' (Icc a b))
    (ha : A a = 0) (hb : A b = 0) (ha' : A' a = 0) (hb' : A' b = 0)
    (hsep : ∀ x ∈ Icc a b, δ ≤ |p x|)
    (hbound0 : ∀ x ∈ Icc a b, ‖A x‖ ≤ C0)
    (hbound1 : ∀ x ∈ Icc a b, ‖A' x‖ ≤ C1)
    (hbound2 : ∀ x ∈ Icc a b, ‖A'' x‖ ≤ C2)
    (hphase1 : ∀ x ∈ Icc a b, |p' x| ≤ P1)
    (hphase2 : ∀ x ∈ Icc a b, |p'' x| ≤ P2) :
    ‖∫ x in a..b, A x * oscillatoryExponential φ x‖ ≤
      (b - a) * (C2 / δ ^ 2 + 3 * C1 * P1 / δ ^ 3 +
        C0 * P2 / δ ^ 3 + 3 * C0 * P1 ^ 2 / δ ^ 4) := by
  have hp0 (x : ℝ) (hx : x ∈ Icc a b) : p x ≠ 0 :=
    abs_pos.mp (hδ.trans_le (hsep x hx))
  have hAc : ContinuousOn A (Icc a b) := fun x hx => (hA x hx).continuousAt.continuousWithinAt
  have hA'c : ContinuousOn A' (Icc a b) := fun x hx => (hA' x hx).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Icc a b) := fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hp'c : ContinuousOn p' (Icc a b) := fun x hx => (hp' x hx).continuousAt.continuousWithinAt
  have hne (k : ℕ) (x : ℝ) (hx : x ∈ Icc a b) : |p x| ^ k ≠ 0 :=
    pow_ne_zero k (abs_ne_zero.mpr (hp0 x hx))
  have hbound : ContinuousOn (fun x =>
      ‖A'' x‖ / |p x| ^ 2 + 3 * ‖A' x‖ * |p' x| / |p x| ^ 3 +
      ‖A x‖ * |p'' x| / |p x| ^ 3 + 3 * ‖A x‖ * |p' x| ^ 2 / |p x| ^ 4)
      (Icc a b) :=
    (((hA''c.norm.div (hpc.abs.pow 2) (hne 2)).add
      (((hA'c.norm.const_mul 3).mul hp'c.abs).div (hpc.abs.pow 3) (hne 3))).add
        ((hAc.norm.mul hp''c.abs).div (hpc.abs.pow 3) (hne 3))).add
          (((hAc.norm.const_mul 3).mul (hp'c.abs.pow 2)).div (hpc.abs.pow 4) (hne 4))
  calc
    _ ≤ ∫ x in a..b, (‖A'' x‖ / |p x| ^ 2 + 3 * ‖A' x‖ * |p' x| / |p x| ^ 3 +
        ‖A x‖ * |p'' x| / |p x| ^ 3 + 3 * ‖A x‖ * |p' x| ^ 2 / |p x| ^ 4) :=
      norm_oscillatory_integral_le_twice_integration_by_parts hab hA hA' hφ hp hp'
        hp0 hA''c hp''c ha hb ha' hb'
    _ ≤ ∫ _x in a..b, (C2 / δ ^ 2 + 3 * C1 * P1 / δ ^ 3 +
        C0 * P2 / δ ^ 3 + 3 * C0 * P1 ^ 2 / δ ^ 4) := by
      apply intervalIntegral.integral_mono_on hab (hbound.intervalIntegrable_of_Icc hab)
        (intervalIntegrable_const)
      intro x hx
      have hd (k : ℕ) : δ ^ k ≤ |p x| ^ k :=
        pow_le_pow_left₀ hδ.le (hsep x hx) k
      apply add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
      · exact div_le_div₀ hC2 (hbound2 x hx) (pow_pos hδ 2) (hd 2)
      · apply div_le_div₀ (by positivity) ?_ (pow_pos hδ 3) (hd 3)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound1 x hx) (by norm_num))
          (hphase1 x hx) (abs_nonneg _) (by positivity)
      · apply div_le_div₀ (by positivity) ?_ (pow_pos hδ 3) (hd 3)
        exact mul_le_mul (hbound0 x hx) (hphase2 x hx) (abs_nonneg _) hC0
      · apply div_le_div₀ (by positivity) ?_ (pow_pos hδ 4) (hd 4)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound0 x hx) (by norm_num))
          (pow_le_pow_left₀ (abs_nonneg _) (hphase1 x hx) 2) (sq_nonneg _) (by positivity)
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]

end ProofProject
