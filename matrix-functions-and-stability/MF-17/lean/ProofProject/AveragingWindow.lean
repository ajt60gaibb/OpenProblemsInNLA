import ProofProject.HilbertFourier
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# The normalized interval window for semigroup Fourier averages

The real window is constant `1 / sqrt N` on `[N/2, 3N/2]` and zero
elsewhere. Its squared integral is one. Multiplication by a continuous
bounded vector-valued orbit preserves the corresponding uniform energy bound.
-/

noncomputable section

namespace ProofProject

open MeasureTheory Set
open scoped ENNReal

/-- The source's real, nonnegative averaging window. -/
def averagingWindow (N : ℝ) : ℝ → ℝ :=
  (Icc (N / 2) (3 * N / 2)).indicator (fun _ => (Real.sqrt N)⁻¹)

theorem averagingWindow_of_mem {N s : ℝ} (hs : s ∈ Icc (N / 2) (3 * N / 2)) :
    averagingWindow N s = (Real.sqrt N)⁻¹ := indicator_of_mem hs _

theorem averagingWindow_of_not_mem {N s : ℝ}
    (hs : s ∉ Icc (N / 2) (3 * N / 2)) : averagingWindow N s = 0 :=
  indicator_of_notMem hs _

theorem averagingWindow_nonneg (N s : ℝ) : 0 ≤ averagingWindow N s := by
  exact indicator_nonneg (fun _ _ => inv_nonneg.mpr (Real.sqrt_nonneg N)) s

theorem averagingWindow_eq_zero_of_neg {N s : ℝ} (hN : 0 < N) (hs : s < 0) :
    averagingWindow N s = 0 := by
  apply averagingWindow_of_not_mem
  intro h
  linarith [h.1]

theorem averagingWindow_support_subset (N : ℝ) :
    Function.support (averagingWindow N) ⊆ Icc (N / 2) (3 * N / 2) :=
  support_indicator_subset

theorem averagingWindow_support_nonneg {N : ℝ} (hN : 0 < N) :
    Function.support (averagingWindow N) ⊆ Ici 0 := by
  intro s hs
  have h := averagingWindow_support_subset N hs
  change 0 ≤ s
  linarith [h.1]

theorem averagingWindow_integrable (N : ℝ) : Integrable (averagingWindow N) := by
  rw [averagingWindow, integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by simp [Real.volume_Icc])

theorem averagingWindow_memLp (N : ℝ) (p : ℝ≥0∞) : MemLp (averagingWindow N) p := by
  exact memLp_indicator_const p measurableSet_Icc _ (Or.inr (by simp [Real.volume_Icc]))

private theorem averagingWindow_measure {N : ℝ} (hN : 0 < N) :
    volume.real (Icc (N / 2) (3 * N / 2)) = N := by
  rw [Real.volume_real_Icc_of_le (by linarith)]
  ring

theorem averagingWindow_integral {N : ℝ} (hN : 0 < N) :
    ∫ s, averagingWindow N s = Real.sqrt N := by
  rw [averagingWindow, integral_indicator_const _ measurableSet_Icc,
    averagingWindow_measure hN, smul_eq_mul]
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  rw [← div_eq_mul_inv]
  apply (div_eq_iff hs).mpr
  simpa only [pow_two] using (Real.sq_sqrt hN.le).symm

theorem averagingWindow_integral_abs {N : ℝ} (hN : 0 < N) :
    ∫ s, |averagingWindow N s| = Real.sqrt N := by
  simpa only [abs_of_nonneg (averagingWindow_nonneg N _)] using
    averagingWindow_integral hN

theorem averagingWindow_integral_sq {N : ℝ} (hN : 0 < N) :
    ∫ s, averagingWindow N s ^ 2 = 1 := by
  have heq : (fun s => averagingWindow N s ^ 2) =
      (Icc (N / 2) (3 * N / 2)).indicator (fun _ => (Real.sqrt N)⁻¹ ^ 2) := by
    funext s
    by_cases hs : s ∈ Icc (N / 2) (3 * N / 2)
    · simp [averagingWindow, hs]
    · simp [averagingWindow, hs]
  rw [heq, integral_indicator_const _ measurableSet_Icc,
    averagingWindow_measure hN, smul_eq_mul, inv_pow, Real.sq_sqrt hN.le]
  exact mul_inv_cancel₀ hN.ne'

section Orbit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem averagingWindow_smul_eq_indicator (N : ℝ) (F : ℝ → E) :
    (fun s => averagingWindow N s • F s) =
      (Icc (N / 2) (3 * N / 2)).indicator (fun s => (Real.sqrt N)⁻¹ • F s) := by
  funext s
  by_cases hs : s ∈ Icc (N / 2) (3 * N / 2) <;> simp [averagingWindow, hs]

theorem averagingWindow_smul_aestronglyMeasurable {N : ℝ} {F : ℝ → E}
    (hF : ContinuousOn F (Icc (N / 2) (3 * N / 2))) :
    AEStronglyMeasurable (fun s => averagingWindow N s • F s) := by
  rw [averagingWindow_smul_eq_indicator,
    aestronglyMeasurable_indicator_iff measurableSet_Icc]
  exact (continuousOn_const.smul hF).aestronglyMeasurable measurableSet_Icc

theorem averagingWindow_smul_norm_le {N C : ℝ} {F : ℝ → E}
    (hbound : ∀ s ∈ Icc (N / 2) (3 * N / 2), ‖F s‖ ≤ C) (s : ℝ) :
    ‖averagingWindow N s • F s‖ ≤ averagingWindow N s * C := by
  by_cases hs : s ∈ Icc (N / 2) (3 * N / 2)
  · rw [norm_smul, Real.norm_of_nonneg (averagingWindow_nonneg N s)]
    exact mul_le_mul_of_nonneg_left (hbound s hs) (averagingWindow_nonneg N s)
  · simp [averagingWindow_of_not_mem hs]

theorem averagingWindow_smul_integrable {N C : ℝ} {F : ℝ → E}
    (hF : ContinuousOn F (Icc (N / 2) (3 * N / 2)))
    (hbound : ∀ s ∈ Icc (N / 2) (3 * N / 2), ‖F s‖ ≤ C) :
    Integrable (fun s => averagingWindow N s • F s) := by
  exact ((averagingWindow_integrable N).mul_const C).mono'
    (averagingWindow_smul_aestronglyMeasurable hF)
    (Filter.Eventually.of_forall (averagingWindow_smul_norm_le hbound))

theorem averagingWindow_smul_norm_sq_le {N C : ℝ} {F : ℝ → E} (hC : 0 ≤ C)
    (hbound : ∀ s ∈ Icc (N / 2) (3 * N / 2), ‖F s‖ ≤ C) (s : ℝ) :
    ‖averagingWindow N s • F s‖ ^ 2 ≤ averagingWindow N s ^ 2 * C ^ 2 := by
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (averagingWindow_nonneg N s) hC)).mpr
      (averagingWindow_smul_norm_le hbound s)

theorem averagingWindow_smul_integrable_norm_sq {N C : ℝ} {F : ℝ → E}
    (hC : 0 ≤ C) (hF : ContinuousOn F (Icc (N / 2) (3 * N / 2)))
    (hbound : ∀ s ∈ Icc (N / 2) (3 * N / 2), ‖F s‖ ≤ C) :
    Integrable (fun s => ‖averagingWindow N s • F s‖ ^ 2) := by
  apply ((averagingWindow_memLp N 2).integrable_sq.mul_const (C ^ 2)).mono'
    ((averagingWindow_smul_aestronglyMeasurable hF).norm.pow 2)
  filter_upwards with s
  simpa only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)] using
    averagingWindow_smul_norm_sq_le hC hbound s

theorem averagingWindow_smul_memLp {N C : ℝ} {F : ℝ → E}
    (hC : 0 ≤ C) (hF : ContinuousOn F (Icc (N / 2) (3 * N / 2)))
    (hbound : ∀ s ∈ Icc (N / 2) (3 * N / 2), ‖F s‖ ≤ C) :
    MemLp (fun s => averagingWindow N s • F s) 2 :=
  (memLp_two_iff_integrable_sq_norm (averagingWindow_smul_aestronglyMeasurable hF)).mpr
    (averagingWindow_smul_integrable_norm_sq hC hF hbound)

theorem averagingWindow_smul_integral_norm_sq_le {N C : ℝ} {F : ℝ → E}
    (hN : 0 < N) (hC : 0 ≤ C) (hF : ContinuousOn F (Icc (N / 2) (3 * N / 2)))
    (hbound : ∀ s ∈ Icc (N / 2) (3 * N / 2), ‖F s‖ ≤ C) :
    (∫ s, ‖averagingWindow N s • F s‖ ^ 2) ≤ C ^ 2 := by
  calc
    _ ≤ ∫ s, averagingWindow N s ^ 2 * C ^ 2 :=
      integral_mono (averagingWindow_smul_integrable_norm_sq hC hF hbound)
        ((averagingWindow_memLp N 2).integrable_sq.mul_const _)
        (averagingWindow_smul_norm_sq_le hC hbound)
    _ = _ := by rw [integral_mul_const, averagingWindow_integral_sq hN, one_mul]

theorem averagingWindow_smul_integral_norm_le {N C : ℝ} {F : ℝ → E}
    (hN : 0 < N) (hF : ContinuousOn F (Icc (N / 2) (3 * N / 2)))
    (hbound : ∀ s ∈ Icc (N / 2) (3 * N / 2), ‖F s‖ ≤ C) :
    (∫ s, ‖averagingWindow N s • F s‖) ≤ C * Real.sqrt N := by
  calc
    _ ≤ ∫ s, averagingWindow N s * C :=
      integral_mono (averagingWindow_smul_integrable hF hbound).norm
        ((averagingWindow_integrable N).mul_const C) (averagingWindow_smul_norm_le hbound)
    _ = _ := by rw [integral_mul_const, averagingWindow_integral hN, mul_comm]

end Orbit

theorem averagingWindow_complex_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (N s : ℝ) (x : E) :
    (averagingWindow N s : ℂ) • x = averagingWindow N s • x :=
  (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

end ProofProject
