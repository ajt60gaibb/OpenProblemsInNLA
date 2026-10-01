import ProofProject.SourceWindowPhaseBounds
import ProofProject.SourceWindowAmplitude
import ProofProject.OscillatoryTwiceIntegration

/-!
# Bounds for the actual scalar Fourier windows

The stationary estimate and the twice-integration-by-parts estimate apply to
concrete rescaled amplitudes.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace ProofProject

/-- If the rescaled amplitude and its derivative have size `C sqrt(Λ)`, the
actual Fourier coefficient has a uniform bound. -/
theorem sourceWindowCoefficient_norm_le_uniform {N C : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    (j : ℕ) (ξ : ℝ)
    (hbound : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2),
      ‖sourceWindowAmplitude N a j w‖ ≤ C * Real.sqrt (sourceWindowScale N j))
    (hbound' : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2),
      ‖deriv (sourceWindowAmplitude N a j) w‖ ≤ C * Real.sqrt (sourceWindowScale N j)) :
    ‖triangularKernelCoefficient N (oscillatoryKernel 1 a) sourceTriangleCutoff j ξ‖ ≤
      52 * C := by
  have hL := sourceWindowScale_pos hN j
  have hκ := sourceWindowCurvature_pos hN j
  have hsκ : 0 < Real.sqrt (sourceWindowCurvature N j) := Real.sqrt_pos.mpr hκ
  have hratio : Real.sqrt (sourceWindowScale N j) ≤
      4 * Real.sqrt (sourceWindowCurvature N j) := by
    have h := sourceWindowScale_le_curvature hN j
    have hsq1 := Real.sq_sqrt hL.le
    have hsq2 := Real.sq_sqrt hκ.le
    have hs1 := Real.sqrt_nonneg (sourceWindowScale N j)
    have hs2 := Real.sqrt_nonneg (sourceWindowCurvature N j)
    nlinarith
  have h := sourceWindowCoefficient_norm_le_of_amplitude_bounds hN (by positivity)
    ha j ξ hbound hbound'
  apply h.trans
  apply (div_le_iff₀ hsκ).mpr
  nlinarith [mul_le_mul_of_nonneg_left hratio hC]

/-- Away from stationary frequencies, two integrations by parts bound the
actual coefficient by the explicit inverse powers of the derivative gap. -/
theorem sourceWindowCoefficient_norm_le_gap {N δ C0 C1 C2 : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (j : ℕ) (ξ : ℝ)
    (hsep : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2), δ ≤ |sourceOscillatoryPhaseDeriv N j ξ w|)
    (hbound0 : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2), ‖sourceWindowAmplitude N a j w‖ ≤ C0)
    (hbound1 : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2),
      ‖deriv (sourceWindowAmplitude N a j) w‖ ≤ C1)
    (hbound2 : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2),
      ‖deriv (deriv (sourceWindowAmplitude N a j)) w‖ ≤ C2) :
    ‖triangularKernelCoefficient N (oscillatoryKernel 1 a) sourceTriangleCutoff j ξ‖ ≤
      3 * (C2 / δ ^ 2 + 3 * C1 * (4 * sourceWindowScale N j) / δ ^ 3 +
        C0 * (24 * sourceWindowScale N j) / δ ^ 3 +
        3 * C0 * (4 * sourceWindowScale N j) ^ 2 / δ ^ 4) := by
  have hL := sourceWindowScale_pos hN j
  have hAd := sourceWindowAmplitude_contDiff N ha j
  have hAd' : ContDiff ℝ ∞ (deriv (sourceWindowAmplitude N a j)) :=
    (contDiff_infty_iff_deriv.mp hAd).2
  have hdom (w : ℝ) (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) : 0 < (j : ℝ) + w := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith [hw.1]
  have hroot : Continuous (fun w : ℝ => Real.sqrt (N * ((j : ℝ) + w))) := by fun_prop
  have hp'' : ContinuousOn (sourceOscillatoryPhaseThird N j) (Icc (1 / 2 : ℝ) (7 / 2)) := by
    unfold sourceOscillatoryPhaseThird
    apply continuousOn_const.div ((hroot.continuousOn.pow 5).const_mul 4)
    intro w hw
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 5 (Real.sqrt_pos.mpr (mul_pos hN (hdom w hw))).ne')
  rw [sourceWindowCoefficient_eq_intervalIntegral hN]
  have h := norm_oscillatory_integral_le_twice_sup
    (by norm_num : (1 / 2 : ℝ) ≤ 7 / 2) hδ hC0 hC1 hC2
    (by positivity : 0 ≤ 4 * sourceWindowScale N j)
    (by positivity : 0 ≤ 24 * sourceWindowScale N j)
    (fun w _ => (hAd.differentiable (by simp)).differentiableAt.hasDerivAt)
    (fun w _ => (hAd'.differentiable (by simp)).differentiableAt.hasDerivAt)
    (fun w hw => sourceOscillatoryPhase_hasDerivAt hN (hdom w hw) ξ)
    (fun w hw => sourceOscillatoryPhaseDeriv_hasDerivAt hN (hdom w hw) ξ)
    (fun w hw => sourceOscillatoryPhaseSecond_hasDerivAt hN (hdom w hw))
    (hAd'.continuous_deriv (by simp)).continuousOn hp''
    (sourceWindowAmplitude_iteratedDeriv_left N a j 0)
    (sourceWindowAmplitude_iteratedDeriv_right N a j 0)
    (sourceWindowAmplitude_iteratedDeriv_left N a j 1)
    (sourceWindowAmplitude_iteratedDeriv_right N a j 1)
    hsep hbound0 hbound1 hbound2
    (fun w hw => abs_sourceWindowPhaseSecond_le hN j hw)
    (fun w hw => abs_sourceWindowPhaseThird_le hN j hw)
  norm_num only [show (7 / 2 : ℝ) - 1 / 2 = 3 by norm_num] at h
  exact h

/-- Inverse-square decay for the actual window, in the normalized derivative
gap. The explicit factor `Λ^(-3/2)` will be bounded using kernel support. -/
theorem sourceWindowCoefficient_norm_le_normalized_gap {N C s : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) (hs : 1 ≤ s)
    {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (j : ℕ) (ξ : ℝ)
    (hsep : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2),
      sourceWindowScale N j * s ≤ |sourceOscillatoryPhaseDeriv N j ξ w|)
    (hbound0 : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2),
      ‖sourceWindowAmplitude N a j w‖ ≤ C * Real.sqrt (sourceWindowScale N j))
    (hbound1 : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2),
      ‖deriv (sourceWindowAmplitude N a j) w‖ ≤ C * Real.sqrt (sourceWindowScale N j))
    (hbound2 : ∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2),
      ‖deriv (deriv (sourceWindowAmplitude N a j)) w‖ ≤
        C * Real.sqrt (sourceWindowScale N j)) :
    ‖triangularKernelCoefficient N (oscillatoryKernel 1 a) sourceTriangleCutoff j ξ‖ ≤
      255 * C / (Real.sqrt (sourceWindowScale N j) ^ 3 * s ^ 2) := by
  let L := sourceWindowScale N j
  have hL : 0 < L := sourceWindowScale_pos hN j
  have hsp : 0 < s := by linarith
  have hr : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have h := sourceWindowCoefficient_norm_le_gap hN (mul_pos hL hsp)
    (by positivity) (by positivity) (by positivity) ha j ξ hsep hbound0 hbound1 hbound2
  have heq (r L' : ℝ) (hr' : r ≠ 0) (he : L' = r ^ 2) :
      3 * (C * r / (L' * s) ^ 2 + 3 * (C * r) * (4 * L') / (L' * s) ^ 3 +
        (C * r) * (24 * L') / (L' * s) ^ 3 +
        3 * (C * r) * (4 * L') ^ 2 / (L' * s) ^ 4) =
      (3 * C / r ^ 3) * (1 / s ^ 2 + 36 / s ^ 3 + 48 / s ^ 4) := by
    rw [he]
    field_simp
    <;> ring
  change ‖_‖ ≤ 3 * (C * Real.sqrt L / (L * s) ^ 2 +
    3 * (C * Real.sqrt L) * (4 * L) / (L * s) ^ 3 +
    (C * Real.sqrt L) * (24 * L) / (L * s) ^ 3 +
    3 * (C * Real.sqrt L) * (4 * L) ^ 2 / (L * s) ^ 4) at h
  rw [heq (Real.sqrt L) L hr.ne' (Real.sq_sqrt hL.le).symm] at h
  have hs3 : s ^ 2 ≤ s ^ 3 := pow_le_pow_right₀ hs (by norm_num)
  have hs4 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  have h3 : 36 / s ^ 3 ≤ 36 / s ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hsp 2) hs3
  have h4 : 48 / s ^ 4 ≤ 48 / s ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hsp 2) hs4
  calc
    _ ≤ (3 * C / Real.sqrt L ^ 3) * (1 / s ^ 2 + 36 / s ^ 3 + 48 / s ^ 4) := h
    _ ≤ (3 * C / Real.sqrt L ^ 3) * (1 / s ^ 2 + 36 / s ^ 2 + 48 / s ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by dsimp only [L]; ring

end ProofProject
