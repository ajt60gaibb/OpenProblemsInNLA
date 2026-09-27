import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Scalar Gaussian small-ball estimates

A peak-density estimate controls intervals when the variance has a positive
lower bound. Away from the mean, a complementary estimate is uniform over all
variances, including zero. This module imports only mathlib; the projection and
planted-phase arguments specialise its results in separate modules.
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section

namespace NLA.FR05

/-- The real-valued Gaussian density is bounded by its normalising constant. -/
theorem gaussianPDFReal_le_peak (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  rw [gaussianPDFReal]
  have harg : -(x - μ) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (sq_nonneg _)
    · positivity
  have hexp : Real.exp (-(x - μ) ^ 2 / (2 * (v : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr harg
  simpa using
    (mul_le_mul_of_nonneg_left hexp
      (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * (v : ℝ)))))

/-- The extended-nonnegative Gaussian density is bounded by its normalising constant. -/
theorem gaussianPDF_le_peak (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDF μ v x ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_peak μ v x)

/-- Bound a Gaussian set probability by peak density times Lebesgue measure. -/
theorem gaussianReal_set_le_peak (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (s : Set ℝ) :
    gaussianReal μ v s ≤
      ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * volume s := by
  rw [gaussianReal_apply μ hv s]
  calc
    ∫⁻ x in s, gaussianPDF μ v x ≤
        ∫⁻ _ in s, ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ :=
      lintegral_mono fun x ↦ gaussianPDF_le_peak μ v x
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * volume s :=
      setLIntegral_const s _

/-- Bound the mass of an interval of radius `u` by its length times peak density. -/
theorem gaussianReal_Icc_smallBall (μ a u : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v (Set.Icc (a - u) (a + u)) ≤
      ENNReal.ofReal (2 * u / Real.sqrt (2 * Real.pi * (v : ℝ))) := by
  calc
    gaussianReal μ v (Set.Icc (a - u) (a + u)) ≤
        ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          volume (Set.Icc (a - u) (a + u)) :=
      gaussianReal_set_le_peak μ hv _
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          ENNReal.ofReal (2 * u) := by
      rw [Real.volume_Icc]
      congr 2
      ring
    _ = ENNReal.ofReal (2 * u / Real.sqrt (2 * Real.pi * (v : ℝ))) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      congr 1
      ring

/-- An interval bound using a positive lower bound on the standard deviation. -/
theorem gaussianReal_Icc_smallBall_of_sq_le (μ a u r : ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) (hu : 0 ≤ u) (hr : 0 < r) (hvar : r ^ 2 ≤ (v : ℝ)) :
    gaussianReal μ v (Set.Icc (a - u) (a + u)) ≤
      ENNReal.ofReal (2 * u / (Real.sqrt (2 * Real.pi) * r)) := by
  have htwo_pi : 0 < 2 * Real.pi := by positivity
  have hroot : r ≤ Real.sqrt (v : ℝ) := by
    exact (Real.le_sqrt hr.le (NNReal.zero_le_coe)).mpr hvar
  have hden : Real.sqrt (2 * Real.pi) * r ≤
      Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    rw [Real.sqrt_mul htwo_pi.le]
    exact mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)
  have hdenpos : 0 < Real.sqrt (2 * Real.pi) * r :=
    mul_pos (Real.sqrt_pos.2 htwo_pi) hr
  have hratio : 2 * u / Real.sqrt (2 * Real.pi * (v : ℝ)) ≤
      2 * u / (Real.sqrt (2 * Real.pi) * r) := by
    exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hu) hdenpos hden
  exact (gaussianReal_Icc_smallBall μ a u hv).trans
    (ENNReal.ofReal_le_ofReal hratio)

/-- The interval bound after rescaling a lower bound on the standard deviation. -/
theorem gaussianReal_Icc_smallBall_of_scaled_sq_le
    (μ a u t S : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hu : 0 ≤ u)
    (ht : 0 < t) (hS : 0 < S)
    (hvar : (t / Real.sqrt S) ^ 2 ≤ (v : ℝ)) :
    gaussianReal μ v (Set.Icc (a - u) (a + u)) ≤
      ENNReal.ofReal (2 * u * Real.sqrt S / (Real.sqrt (2 * Real.pi) * t)) := by
  have hsqrtS : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hr : 0 < t / Real.sqrt S := div_pos ht hsqrtS
  have hsmall := gaussianReal_Icc_smallBall_of_sq_le μ a u
    (t / Real.sqrt S) hv hu hr hvar
  have heq :
      2 * u / (Real.sqrt (2 * Real.pi) * (t / Real.sqrt S)) =
        2 * u * Real.sqrt S / (Real.sqrt (2 * Real.pi) * t) := by
    field_simp [hsqrtS.ne', ht.ne']
  simpa only [heq] using hsmall

/-- The source-ready form: if the unscaled variance `V` is at least `t²`,
then a Gaussian of variance `V / S` has the stated interval small-ball bound. -/
theorem gaussianReal_Icc_smallBall_of_real_variance
    (μ a u t V S : ℝ) (hu : 0 ≤ u) (ht : 0 < t) (hS : 0 < S)
    (hV : t ^ 2 ≤ V) :
    gaussianReal μ ⟨V / S, div_nonneg (le_trans (sq_nonneg t) hV) hS.le⟩
        (Set.Icc (a - u) (a + u)) ≤
      ENNReal.ofReal (2 * u * Real.sqrt S / (Real.sqrt (2 * Real.pi) * t)) := by
  let v : ℝ≥0 := ⟨V / S, div_nonneg (le_trans (sq_nonneg t) hV) hS.le⟩
  have htSq : 0 < t ^ 2 := sq_pos_of_pos ht
  have hVpos : 0 < V := lt_of_lt_of_le htSq hV
  have hv : v ≠ 0 := by
    exact ne_of_gt (by
      exact div_pos hVpos hS)
  have hvar : (t / Real.sqrt S) ^ 2 ≤ (v : ℝ) := by
    change (t / Real.sqrt S) ^ 2 ≤ V / S
    calc
      (t / Real.sqrt S) ^ 2 = t ^ 2 / S := by
        rw [div_pow, Real.sq_sqrt hS.le]
      _ ≤ V / S := div_le_div_of_nonneg_right hV hS.le
  simpa only [v] using
    (gaussianReal_Icc_smallBall_of_scaled_sq_le μ a u t S hv hu ht hS hvar)

/-- A coarse bound for the square-root factor times exponential decay. -/
lemma sqrt_mul_exp_neg_le_one (z : ℝ) (hz : 0 ≤ z) :
    Real.sqrt z * Real.exp (-z) ≤ 1 := by
  have hsqrt : Real.sqrt z ≤ z + 1 := by
    nlinarith [Real.sq_sqrt hz, sq_nonneg (Real.sqrt z - 1)]
  calc
    _ ≤ Real.exp z * Real.exp (-z) :=
      mul_le_mul_of_nonneg_right (hsqrt.trans (Real.add_one_le_exp z)) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- Away from zero, Gaussian decay controls the inverse square root of the variance. -/
lemma exp_neg_div_sqrt_variance_le (t r : ℝ)
    (ht : 0 < t) (hr : 0 < r) :
    (Real.sqrt r)⁻¹ * Real.exp (-(t ^ 2 / (8 * r))) ≤ 3 / t := by
  let z : ℝ := t ^ 2 / (8 * r)
  have hz : 0 ≤ z := by
    dsimp [z]
    positivity
  have hcore : Real.sqrt z * Real.exp (-z) ≤ 1 := sqrt_mul_exp_neg_le_one z hz
  have hsqrtr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsqrt8 : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have hrootz : Real.sqrt z = t / (Real.sqrt 8 * Real.sqrt r) := by
    dsimp [z]
    rw [Real.sqrt_div (sq_nonneg t)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
  have hroot8 : Real.sqrt 8 ≤ 3 := by
    exact (Real.sqrt_le_iff).mpr (by norm_num)
  have hmain : (Real.sqrt r)⁻¹ * Real.exp (-z) ≤ Real.sqrt 8 / t := by
    rw [hrootz] at hcore
    have hfactor : 0 ≤ Real.sqrt 8 / t :=
      (div_pos hsqrt8 ht).le
    have heq : (Real.sqrt r)⁻¹ * Real.exp (-z) =
        (Real.sqrt 8 / t) *
          ((t / (Real.sqrt 8 * Real.sqrt r)) * Real.exp (-z)) := by
      field_simp [hsqrtr.ne', hsqrt8.ne', ht.ne']
    rw [heq]
    calc
      (Real.sqrt 8 / t) *
          ((t / (Real.sqrt 8 * Real.sqrt r)) * Real.exp (-z)) ≤
          (Real.sqrt 8 / t) * 1 :=
        mul_le_mul_of_nonneg_left hcore hfactor
      _ = Real.sqrt 8 / t := by ring
  calc
    (Real.sqrt r)⁻¹ * Real.exp (-(t ^ 2 / (8 * r))) =
        (Real.sqrt r)⁻¹ * Real.exp (-z) := by rfl
    _ ≤ Real.sqrt 8 / t := hmain
    _ ≤ 3 / t := by
      exact div_le_div_of_nonneg_right hroot8 ht.le

/-- A centred Gaussian density bound uniform over positive variances away from zero. -/
lemma gaussianPDFReal_zero_le_three_div_of_abs_ge_half
    (t x : ℝ) {v : ℝ≥0} (ht : 0 < t) (hv : v ≠ 0)
    (hx : t / 2 ≤ |x|) :
    gaussianPDFReal 0 v x ≤ 3 / (Real.sqrt (2 * Real.pi) * t) := by
  let r : ℝ := (v : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hsqrtr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have htwoPi : 0 ≤ 2 * Real.pi := Real.two_pi_pos.le
  have hsqrtTwoPi : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 Real.two_pi_pos
  have hrootden : Real.sqrt (2 * Real.pi * r) =
      Real.sqrt (2 * Real.pi) * Real.sqrt r :=
    Real.sqrt_mul htwoPi r
  have hxsq : (t / 2) ^ 2 ≤ x ^ 2 := by
    have habsSq : (t / 2) ^ 2 ≤ |x| ^ 2 := by
      exact (sq_le_sq₀ (by positivity) (abs_nonneg x)).mpr hx
    simpa only [sq_abs] using habsSq
  have hdiv : t ^ 2 / (8 * r) ≤ x ^ 2 / (2 * r) := by
    calc
      t ^ 2 / (8 * r) = (t / 2) ^ 2 / (2 * r) := by
        field_simp [hr.ne']
        ring
      _ ≤ x ^ 2 / (2 * r) :=
        div_le_div_of_nonneg_right hxsq (by positivity)
  have hexp' : Real.exp (-(x ^ 2 / (2 * r))) ≤
      Real.exp (-(t ^ 2 / (8 * r))) :=
    Real.exp_le_exp.mpr (neg_le_neg hdiv)
  have hexp : Real.exp (-x ^ 2 / (2 * r)) ≤
      Real.exp (-(t ^ 2 / (8 * r))) := by
    simpa only [neg_div] using hexp'
  rw [gaussianPDFReal]
  change (Real.sqrt (2 * Real.pi * r))⁻¹ *
      Real.exp (-(x - 0) ^ 2 / (2 * r)) ≤
        3 / (Real.sqrt (2 * Real.pi) * t)
  simp only [sub_zero]
  rw [hrootden, mul_inv_rev]
  calc
    (Real.sqrt r)⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-x ^ 2 / (2 * r)) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ((Real.sqrt r)⁻¹ * Real.exp (-x ^ 2 / (2 * r))) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ *
        ((Real.sqrt r)⁻¹ * Real.exp (-(t ^ 2 / (8 * r)))) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr hsqrtr.le)
      · exact inv_nonneg.mpr hsqrtTwoPi.le
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (3 / t) :=
      mul_le_mul_of_nonneg_left (exp_neg_div_sqrt_variance_le t r ht hr)
        (inv_nonneg.mpr hsqrtTwoPi.le)
    _ = 3 / (Real.sqrt (2 * Real.pi) * t) := by
      field_simp [hsqrtTwoPi.ne', ht.ne']

/-- A Gaussian interval centred at `-m`, uniformly over its (possibly zero)
variance, is small when the centre is separated from zero.  The deliberately
coarse constant is enough for the source's non-tail `u^(1/3)` balance. -/
theorem gaussianReal_abs_add_smallBall_uniform
    (m u t : ℝ) {v : ℝ≥0} (ht : 0 < t)
    (hcentre : t ≤ |m|) (hscale : 2 * u ≤ t) :
    gaussianReal 0 v {x : ℝ | |m + x| ≤ u} ≤
      ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  let s : Set ℝ := {x : ℝ | |m + x| ≤ u}
  have hs : s = Icc (-m - u) (-m + u) := by
    rw [← Real.closedBall_eq_Icc]
    ext x
    simp only [s, Set.mem_ofPred_eq, Metric.mem_closedBall, Real.dist_eq,
      sub_neg_eq_add, add_comm]
  change gaussianReal 0 v s ≤ _
  by_cases hv : v = 0
  · rw [hv, gaussianReal_zero_var]
    have hnot : (0 : ℝ) ∉ s := by
      intro hzero
      dsimp [s] at hzero
      have hlt : u < t := by linarith
      have hm : |m| ≤ u := by simpa using hzero
      linarith
    have hdirac : Measure.dirac (0 : ℝ) s = 0 := by
      rw [MeasureTheory.Measure.dirac_apply]
      simp only [Set.indicator, hnot, if_false]
    rw [hdirac]
    exact bot_le
  · rw [gaussianReal_apply 0 hv s]
    have hsqrtTwoPi : 0 < Real.sqrt (2 * Real.pi) :=
      Real.sqrt_pos.2 Real.two_pi_pos
    have hpoint : ∀ x : ℝ, x ∈ s →
        gaussianPDF 0 v x ≤
          ENNReal.ofReal (3 / (Real.sqrt (2 * Real.pi) * t)) := by
      intro x hx
      have hxbound : |m + x| ≤ u := by
        simpa only [s, Set.mem_ofPred_eq] using hx
      have hmx : |m| ≤ u + |x| := by
        calc
          |m| = |(m + x) - x| := by
            congr 1
            ring
          _ ≤ |m + x| + |x| := by
            exact abs_sub (m + x) x
          _ ≤ u + |x| := by
            linarith
      have hhalf : t / 2 ≤ |x| := by linarith
      exact ENNReal.ofReal_le_ofReal
        (gaussianPDFReal_zero_le_three_div_of_abs_ge_half t x ht hv hhalf)
    calc
      ∫⁻ x in s, gaussianPDF 0 v x ≤
          ∫⁻ _x in s, ENNReal.ofReal
            (3 / (Real.sqrt (2 * Real.pi) * t)) :=
        MeasureTheory.setLIntegral_mono_ae (by fun_prop)
          (Filter.Eventually.of_forall fun x hx ↦ hpoint x hx)
      _ = ENNReal.ofReal (3 / (Real.sqrt (2 * Real.pi) * t)) * volume s :=
        setLIntegral_const s _
      _ = ENNReal.ofReal (3 / (Real.sqrt (2 * Real.pi) * t)) *
          ENNReal.ofReal (2 * u) := by
        rw [hs, Real.volume_Icc]
        congr 2
        ring
      _ = ENNReal.ofReal
          ((3 / (Real.sqrt (2 * Real.pi) * t)) * (2 * u)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
        congr 1
        field_simp [hsqrtTwoPi.ne', ht.ne']
        ring

end NLA.FR05
