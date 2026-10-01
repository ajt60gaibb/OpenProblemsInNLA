import ProofProject.SourceOscillatoryPhase
import ProofProject.OscillatoryKernel
import ProofProject.TrianglePartition
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Exact rescaling of the source Fourier windows

The change of variables `v = N*w` supplies the Jacobian `N` and the exact
phase already differentiated in `SourceOscillatoryPhase`. The signed identity
is valid for every real sign parameter, and hence covers both source phases.
-/

noncomputable section

namespace ProofProject

open MeasureTheory
open scoped ContDiff

/-- The actual rescaled amplitude, including the positive Jacobian. -/
def sourceWindowAmplitude (N : ℝ) (a : ℝ → ℂ) (j : ℕ) (w : ℝ) : ℂ :=
  (N : ℂ) * a (N * ((j : ℝ) + w)) * sourceTriangleCutoff w

private theorem integral_eq_mul_integral_comp {N : ℝ} (hN : 0 < N) (f : ℝ → ℂ) :
    (∫ v : ℝ, f v) = (N : ℂ) * ∫ w : ℝ, f (N * w) := by
  rw [Measure.integral_comp_mul_left f N, abs_of_pos (inv_pos.mpr hN),
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hN.ne', Complex.ofReal_one, one_mul]

/-- The Fourier-window change of variables with either sign and the exact
Mathlib frequency normalization. -/
theorem triangularKernelCoefficient_oscillatory_rescale {N : ℝ} (hN : 0 < N)
    (σ : ℝ) (a : ℝ → ℂ) (j : ℕ) (ξ : ℝ) :
    triangularKernelCoefficient N (oscillatoryKernel σ a) sourceTriangleCutoff j ξ =
      (N : ℂ) * ∫ w : ℝ,
        a (N * ((j : ℝ) + w)) * sourceTriangleCutoff w *
          Complex.exp (((σ * 2 * Real.sqrt (N * ((j : ℝ) + w)) +
            2 * Real.pi * N * ξ * w : ℝ) : ℂ) * Complex.I) := by
  rw [triangularKernelCoefficient_eq_integral]
  rw [integral_eq_mul_integral_comp hN]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with w
  rw [show N * w + (j : ℝ) * N = N * ((j : ℝ) + w) by ring,
    mul_div_cancel_left₀ _ hN.ne']
  unfold oscillatoryKernel
  rw [show 2 * Real.pi * (N * w) * ξ = 2 * Real.pi * N * ξ * w by ring]
  simp only [Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- The positive source phase agrees exactly with the previously formalized
phase, with the Jacobian displayed outside the integral. -/
theorem sourceWindowCoefficient_rescale {N : ℝ} (hN : 0 < N)
    (a : ℝ → ℂ) (j : ℕ) (ξ : ℝ) :
    triangularKernelCoefficient N (oscillatoryKernel 1 a) sourceTriangleCutoff j ξ =
      (N : ℂ) * ∫ w : ℝ,
        a (N * ((j : ℝ) + w)) * sourceTriangleCutoff w *
          Complex.exp ((sourceOscillatoryPhase N j ξ w : ℂ) * Complex.I) := by
  simpa only [one_mul, sourceOscillatoryPhase] using
    triangularKernelCoefficient_oscillatory_rescale hN 1 a j ξ

/-- The same identity in the amplitude-times-phase form used by the scalar
oscillatory estimates. -/
theorem sourceWindowCoefficient_eq_integral {N : ℝ} (hN : 0 < N)
    (a : ℝ → ℂ) (j : ℕ) (ξ : ℝ) :
    triangularKernelCoefficient N (oscillatoryKernel 1 a) sourceTriangleCutoff j ξ =
      ∫ w : ℝ, sourceWindowAmplitude N a j w *
        Complex.exp ((sourceOscillatoryPhase N j ξ w : ℂ) * Complex.I) := by
  rw [sourceWindowCoefficient_rescale hN]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [sourceWindowAmplitude, mul_assoc]

theorem sourceWindowAmplitude_continuous (N : ℝ) {a : ℝ → ℂ}
    (ha : Continuous a) (j : ℕ) : Continuous (sourceWindowAmplitude N a j) := by
  have hζ := sourceTriangleCutoff_contDiff.continuous
  unfold sourceWindowAmplitude
  fun_prop

theorem sourceWindowAmplitude_contDiff (N : ℝ) {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) (j : ℕ) : ContDiff ℝ ∞ (sourceWindowAmplitude N a j) := by
  have hζ := sourceTriangleCutoff_contDiff
  unfold sourceWindowAmplitude
  fun_prop

theorem sourceWindowAmplitude_hasCompactSupport (N : ℝ) (a : ℝ → ℂ) (j : ℕ) :
    HasCompactSupport (sourceWindowAmplitude N a j) :=
  sourceTriangleCutoff_hasCompactSupport.mul_left

theorem sourceWindowAmplitude_tsupport_subset (N : ℝ) (a : ℝ → ℂ) (j : ℕ) :
    tsupport (sourceWindowAmplitude N a j) ⊆ Set.Ioo (1 / 2 : ℝ) (7 / 2) := by
  exact tsupport_mul_subset_right.trans sourceTriangleCutoff_tsupport_subset

/-- The compact cutoff restricts the actual coefficient to the fixed interval
used by the derivative estimates. No smoothness is needed for this identity. -/
theorem sourceWindowCoefficient_eq_intervalIntegral {N : ℝ} (hN : 0 < N)
    (a : ℝ → ℂ) (j : ℕ) (ξ : ℝ) :
    triangularKernelCoefficient N (oscillatoryKernel 1 a) sourceTriangleCutoff j ξ =
      ∫ w in (1 / 2 : ℝ)..(7 / 2), sourceWindowAmplitude N a j w *
        Complex.exp ((sourceOscillatoryPhase N j ξ w : ℂ) * Complex.I) := by
  rw [sourceWindowCoefficient_eq_integral hN]
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro w hw
  have ha : w ∈ Function.support (sourceWindowAmplitude N a j) :=
    Function.support_mul_subset_left _ _ hw
  have ht := sourceWindowAmplitude_tsupport_subset N a j (subset_closure ha)
  exact ⟨ht.1, ht.2.le⟩

/-- Continuity of the amplitude alone ensures convergence of the rescaled
oscillatory integral, since the fixed cutoff has compact support. -/
theorem sourceWindow_integrable (N : ℝ) {a : ℝ → ℂ}
    (ha : Continuous a) (j : ℕ) (ξ : ℝ) :
    Integrable (fun w : ℝ => sourceWindowAmplitude N a j w *
      Complex.exp ((sourceOscillatoryPhase N j ξ w : ℂ) * Complex.I)) := by
  have hc : Continuous (fun w : ℝ =>
      Complex.exp ((sourceOscillatoryPhase N j ξ w : ℂ) * Complex.I)) := by
    unfold sourceOscillatoryPhase
    fun_prop
  exact ((sourceWindowAmplitude_continuous N ha j).mul hc).integrable_of_hasCompactSupport
    ((sourceWindowAmplitude_hasCompactSupport N a j).mul_right)

theorem sourceWindowAmplitude_norm_le {N : ℝ} (hN : 0 ≤ N)
    (a : ℝ → ℂ) (j : ℕ) (w : ℝ) :
    ‖sourceWindowAmplitude N a j w‖ ≤ N * ‖a (N * ((j : ℝ) + w))‖ := by
  rw [sourceWindowAmplitude, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hN]
  exact mul_le_of_le_one_right (mul_nonneg hN (norm_nonneg _))
    (sourceTriangleCutoff_norm_le_one w)

/-- Conjugation fixes the actual real-valued cutoff. -/
@[simp] theorem sourceTriangleCutoff_star (w : ℝ) :
    star (sourceTriangleCutoff w) = sourceTriangleCutoff w := by
  simp [sourceTriangleCutoff]

/-- Phase reversal conjugates the complex amplitude and reflects the Fourier
frequency. This identity holds for every real scaling parameter. -/
theorem sourceWindowCoefficient_neg_eq_star (N σ : ℝ) (a : ℝ → ℂ)
    (j : ℕ) (ξ : ℝ) :
    triangularKernelCoefficient N (oscillatoryKernel (-σ) a) sourceTriangleCutoff j ξ =
      star (triangularKernelCoefficient N
        (oscillatoryKernel σ (fun u => star (a u))) sourceTriangleCutoff j (-ξ)) := by
  simp_rw [triangularKernelCoefficient_eq_integral]
  rw [← starRingEnd_apply, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with v
  simp [oscillatoryKernel, sourceTriangleCutoff, ← Complex.exp_conj,
    map_ofNat, mul_neg, neg_mul]

theorem sourceWindowCoefficient_neg_norm (N σ : ℝ) (a : ℝ → ℂ)
    (j : ℕ) (ξ : ℝ) :
    ‖triangularKernelCoefficient N (oscillatoryKernel (-σ) a) sourceTriangleCutoff j ξ‖ =
      ‖triangularKernelCoefficient N
        (oscillatoryKernel σ (fun u => star (a u))) sourceTriangleCutoff j (-ξ)‖ := by
  rw [sourceWindowCoefficient_neg_eq_star, norm_star]

end ProofProject
