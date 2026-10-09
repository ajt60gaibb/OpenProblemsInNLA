import ProofProject.SourceWindowRescaling
import ProofProject.OscillatorySecondDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The second-derivative estimate for the actual source windows

The curvature lower bound is the exact value at the right endpoint of the
fixed cutoff interval. In particular it is positive and independent of the
Fourier frequency. The scalar amplitude bounds in the final theorem refer
to the actual rescaled amplitude, including the Jacobian.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace ProofProject

/-- A positive lower bound for the absolute phase curvature throughout the
fixed source window. -/
def sourceWindowCurvature (N : ℝ) (j : ℕ) : ℝ :=
  N ^ 2 / (2 * Real.sqrt (N * ((j : ℝ) + 7 / 2)) ^ 3)

theorem sourceWindowCurvature_pos {N : ℝ} (hN : 0 < N) (j : ℕ) :
    0 < sourceWindowCurvature N j := by
  unfold sourceWindowCurvature
  have hj : 0 < (j : ℝ) + 7 / 2 := by positivity
  have hs : 0 < Real.sqrt (N * ((j : ℝ) + 7 / 2)) :=
    Real.sqrt_pos.mpr (mul_pos hN hj)
  positivity

theorem sourceOscillatoryPhaseSecond_le_neg_curvature {N w : ℝ} (hN : 0 < N)
    (j : ℕ) (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    sourceOscillatoryPhaseSecond N j w ≤ -sourceWindowCurvature N j := by
  have hjw : 0 < (j : ℝ) + w := by have := Nat.cast_nonneg (α := ℝ) j; linarith [hw.1]
  have hsmall : 0 < Real.sqrt (N * ((j : ℝ) + w)) := Real.sqrt_pos.mpr (mul_pos hN hjw)
  have hs : Real.sqrt (N * ((j : ℝ) + w)) ≤
      Real.sqrt (N * ((j : ℝ) + 7 / 2)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (by linarith [hw.2]) hN.le
  unfold sourceOscillatoryPhaseSecond sourceWindowCurvature
  rw [neg_div]
  apply neg_le_neg
  apply div_le_div_of_nonneg_left (sq_nonneg N) (by positivity)
  gcongr

theorem norm_sourcePhase_integral_le {N C C' : ℝ} (hN : 0 < N) (hC : 0 ≤ C)
    (j : ℕ) (ξ : ℝ) {A A' : ℝ → ℂ}
    (hA : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2), HasDerivAt A (A' w) w)
    (hA' : ContinuousOn A' (Icc (1 / 2 : ℝ) (7 / 2)))
    (hbound : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2), ‖A w‖ ≤ C)
    (hbound' : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2), ‖A' w‖ ≤ C') :
    ‖∫ w in (1 / 2 : ℝ)..(7 / 2), A w *
      oscillatoryExponential (sourceOscillatoryPhase N j ξ) w‖ ≤
      (10 * C + 3 * C') / Real.sqrt (sourceWindowCurvature N j) := by
  have hab : (1 / 2 : ℝ) ≤ 7 / 2 := by norm_num
  have hdom (w : ℝ) (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) : 0 < (j : ℝ) + w := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith [hw.1]
  have hp' : ContinuousOn (sourceOscillatoryPhaseSecond N j) (Icc (1 / 2 : ℝ) (7 / 2)) :=
    fun w hw => (sourceOscillatoryPhaseSecond_hasDerivAt hN (hdom w hw)).continuousAt.continuousWithinAt
  have hvar : (∫ w in (1 / 2 : ℝ)..(7 / 2), ‖A' w‖) ≤ 3 * C' := by
    calc
      _ ≤ ∫ _w in (1 / 2 : ℝ)..(7 / 2), C' :=
        intervalIntegral.integral_mono_on hab (hA'.norm.intervalIntegrable_of_Icc hab)
          intervalIntegrable_const hbound'
      _ = _ := by rw [intervalIntegral.integral_const]; norm_num
  have h := norm_oscillatory_integral_le_second_derivative hab
    (sourceWindowCurvature_pos hN j) hC hA
    (fun w hw => sourceOscillatoryPhase_hasDerivAt hN (hdom w hw) ξ)
    (fun w hw => sourceOscillatoryPhaseDeriv_hasDerivAt hN (hdom w hw) ξ)
    hA' hp' hbound
    (Or.inr (fun w hw => sourceOscillatoryPhaseSecond_le_neg_curvature hN j hw))
  exact h.trans (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

/-- Apply the second-derivative test to the actual Fourier coefficient. The
bounds concern the concrete rescaled amplitude and its derivative. -/
theorem sourceWindowCoefficient_norm_le_of_amplitude_bounds {N C C' : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    (j : ℕ) (ξ : ℝ)
    (hbound : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2), ‖sourceWindowAmplitude N a j w‖ ≤ C)
    (hbound' : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2),
      ‖deriv (sourceWindowAmplitude N a j) w‖ ≤ C') :
    ‖triangularKernelCoefficient N (oscillatoryKernel 1 a) sourceTriangleCutoff j ξ‖ ≤
      (10 * C + 3 * C') / Real.sqrt (sourceWindowCurvature N j) := by
  rw [sourceWindowCoefficient_eq_intervalIntegral hN]
  have hAd := sourceWindowAmplitude_contDiff N ha j
  exact norm_sourcePhase_integral_le hN hC j ξ
    (fun w _ => (hAd.differentiable (by simp)).differentiableAt.hasDerivAt)
    (hAd.continuous_deriv (by simp)).continuousOn hbound hbound'

end ProofProject
