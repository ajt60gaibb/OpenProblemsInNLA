import ProofProject.GammaKernel
import ProofProject.BesselKernelSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The exact integrable gamma series for the damped Bessel kernel

The integrated absolute majorant is `exp t - 1`. This proves integrability
for every positive `t`, independently of the later oscillatory asymptotic.
No pointwise exponential-in-`u` majorant is used for integration.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

def weightedGammaTerm (t : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  (((-t) ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ) : ℂ) * gammaKernel n (1 / t) u

def besselDampedKernel (t : ℝ) (u : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator
    (fun u => ((Real.exp (-u / t) * besselKernel u : ℝ) : ℂ)) u

theorem besselDampedKernel_of_pos (t : ℝ) {u : ℝ} (hu : 0 < u) :
    besselDampedKernel t u = ((Real.exp (-u / t) * besselKernel u : ℝ) : ℂ) :=
  indicator_of_mem hu _

@[simp] theorem besselDampedKernel_of_nonpos (t : ℝ) {u : ℝ} (hu : u ≤ 0) :
    besselDampedKernel t u = 0 := indicator_of_notMem (not_lt_of_ge hu) _

@[simp] theorem weightedGammaTerm_of_nonpos (t : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ 0) :
    weightedGammaTerm t n u = 0 := by
  simp only [weightedGammaTerm, gammaKernel_of_nonpos n (1 / t) hu, mul_zero]

theorem weightedGammaTerm_integrable (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (weightedGammaTerm t n) :=
  (gammaKernel_integrable n (one_div_pos.mpr ht)).const_mul _

theorem norm_weightedGammaCoefficient (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖(((-t) ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ) : ℂ)‖ =
      t ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  simp only [Complex.norm_real, norm_div, norm_pow, norm_neg,
    Real.norm_of_nonneg ht, Real.norm_of_nonneg (Nat.cast_nonneg _)]

theorem integral_norm_weightedGammaTerm (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ, ‖weightedGammaTerm t n u‖) =
      t ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  simp only [weightedGammaTerm, norm_mul]
  rw [integral_const_mul, integral_norm_gammaKernel n (one_div_pos.mpr ht), mul_one]
  exact norm_weightedGammaCoefficient n ht.le

/-- The scalar exponential series with its zeroth term removed. -/
theorem gammaSeries_norm_majorant_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => t ^ (n + 1) / ((n + 1).factorial : ℝ)) (Real.exp t - 1) := by
  have h : HasSum (fun n : ℕ => t ^ n / (n.factorial : ℝ)) (Real.exp t) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp t
  simpa only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    using (hasSum_nat_add_iff' 1).mpr h

theorem weightedGammaTerm_integral_norm_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => ∫ u : ℝ, ‖weightedGammaTerm t n u‖) (Real.exp t - 1) := by
  simpa only [integral_norm_weightedGammaTerm _ ht] using gammaSeries_norm_majorant_hasSum t

theorem weightedGammaTerm_integral_norm_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖weightedGammaTerm t n u‖) :=
  (weightedGammaTerm_integral_norm_hasSum ht).summable

theorem tsum_integral_norm_weightedGammaTerm {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, ∫ u : ℝ, ‖weightedGammaTerm t n u‖) = Real.exp t - 1 :=
  (weightedGammaTerm_integral_norm_hasSum ht).tsum_eq

/-- The powers of the rate cancel the powers of time exactly. -/
theorem weightedGammaTerm_of_pos {t : ℝ} (ht : 0 < t) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    weightedGammaTerm t n u = ((-Real.exp (-u / t) * besselTerm n u : ℝ) : ℂ) := by
  rw [weightedGammaTerm, gammaKernel_of_pos n (1 / t) hu, ← Complex.ofReal_mul]
  congr 1
  have hp : (-t) ^ (n + 1) * (1 / t) ^ (n + 1) = -((-1 : ℝ) ^ n) := by
    rw [← mul_pow, show (-t) * (1 / t) = -1 by field_simp [ht.ne'],
      pow_succ]
    ring
  have he : -(1 / t) * u = -u / t := by ring
  rw [he]
  calc
    _ = ((-t) ^ (n + 1) * (1 / t) ^ (n + 1)) * Real.exp (-u / t) * u ^ n /
        ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hp]; unfold besselTerm; ring

theorem weightedGammaTerm_hasSum {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasSum (fun n : ℕ => weightedGammaTerm t n u) (-besselDampedKernel t u) := by
  by_cases hu : 0 < u
  · have h := Complex.hasSum_ofReal.mpr ((besselTerm_hasSum u).mul_left (-Real.exp (-u / t)))
    have h' := h.congr_fun (fun n => weightedGammaTerm_of_pos ht n hu)
    simpa only [besselDampedKernel_of_pos t hu, neg_mul, Complex.ofReal_neg] using h'
  · have hu0 := le_of_not_gt hu
    simp only [weightedGammaTerm_of_nonpos t _ hu0, besselDampedKernel_of_nonpos t hu0,
      neg_zero]
    exact hasSum_zero

theorem tsum_weightedGammaTerm {t : ℝ} (ht : 0 < t) (u : ℝ) :
    (∑' n : ℕ, weightedGammaTerm t n u) = -besselDampedKernel t u :=
  (weightedGammaTerm_hasSum ht u).tsum_eq

theorem weightedGammaTerm_summable {t : ℝ} (ht : 0 < t) (u : ℝ) :
    Summable (fun n : ℕ => weightedGammaTerm t n u) :=
  (weightedGammaTerm_hasSum ht u).summable

theorem weightedGammaTerm_norm_summable {t : ℝ} (ht : 0 < t) (u : ℝ) :
    Summable (fun n : ℕ => ‖weightedGammaTerm t n u‖) := by
  by_cases hu : 0 < u
  · have heq (n : ℕ) : ‖weightedGammaTerm t n u‖ =
        Real.exp (-u / t) * ‖besselTerm n u‖ := by
      rw [weightedGammaTerm_of_pos ht n hu, Complex.norm_real, norm_mul, norm_neg,
        Real.norm_of_nonneg (Real.exp_pos _).le]
    simp_rw [heq]
    exact (besselTerm_norm_summable u).mul_left _
  · simp only [weightedGammaTerm_of_nonpos t _ (le_of_not_gt hu), norm_zero]
    exact summable_zero

/-- Exact integral of the pointwise absolute-series majorant. -/
theorem integral_tsum_norm_weightedGammaTerm {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ, ∑' n : ℕ, ‖weightedGammaTerm t n u‖) = Real.exp t - 1 := by
  have hsum : Summable (fun n : ℕ => ∫ u : ℝ, ‖‖weightedGammaTerm t n u‖‖) := by
    simpa only [norm_norm] using weightedGammaTerm_integral_norm_summable ht
  have h := hasSum_integral_of_summable_integral_norm
    (fun n => (weightedGammaTerm_integrable n ht).norm) hsum
  exact h.unique (weightedGammaTerm_integral_norm_hasSum ht)

/-- The absolute-series dominator is integrable because its exact integral
is positive and finite. This invokes Mathlib's total-integral convention in
the sound direction: a nonzero integral forces genuine integrability. -/
theorem tsum_norm_weightedGammaTerm_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ℝ => ∑' n : ℕ, ‖weightedGammaTerm t n u‖) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_tsum_norm_weightedGammaTerm ht]
  exact ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht))

theorem besselDampedKernel_aestronglyMeasurable (t : ℝ) :
    AEStronglyMeasurable (besselDampedKernel t) volume := by
  have hc : Continuous (fun u : ℝ => ((Real.exp (-u / t) * besselKernel u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (((continuous_id.neg.div_const t).rexp).mul besselKernel_continuous)
  exact hc.aestronglyMeasurable.indicator measurableSet_Ioi

/-- Integrability for every positive damping time follows from the integrated
gamma majorant, and does not depend on any asymptotic estimate for `b`. -/
theorem besselDampedKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (besselDampedKernel t) := by
  apply (tsum_norm_weightedGammaTerm_integrable ht).mono'
    (besselDampedKernel_aestronglyMeasurable t)
  exact Filter.Eventually.of_forall fun u => by
    have h := norm_tsum_le_tsum_norm (weightedGammaTerm_norm_summable ht u)
    simpa only [tsum_weightedGammaTerm ht u, norm_neg] using h

theorem tsum_weightedGammaTerm_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ℝ => ∑' n : ℕ, weightedGammaTerm t n u) := by
  exact (besselDampedKernel_integrable ht).neg.congr
    (Filter.Eventually.of_forall fun u => (tsum_weightedGammaTerm ht u).symm)

end ProofProject
