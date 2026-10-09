import ProofProject.SourceWindowSupportScale
import ProofProject.SourceWeightedAmplitude

/-!
# A uniform inverse-square window estimate

The scale floor is applied only to nonzero windows. Combining the stationary
and nonstationary estimates then gives one bound in every nonnegative gap
parameter, with an absolute constant independent of the window index.
-/

noncomputable section
open Set
open scoped ContDiff
namespace ProofProject

/-- A gap lower bound valid throughout the window supplies a smoothed
inverse-square estimate. This statement avoids selecting a closest frequency. -/
theorem sourceWindowCoefficient_norm_le_smoothed_gap {N C s : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) (hs : 0 ≤ s)
    {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (j : ℕ) (ξ : ℝ)
    (hsupp : ∀ u : ℝ, 4 * N ^ (4 / 3 : ℝ) < u → a u = 0)
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
      522240 * C / (1 + s) ^ 2 := by
  have hden : 0 < (1 + s) ^ 2 := pow_pos (by linarith) 2
  by_cases hz : sourceWindowAmplitude N a j = 0
  · rw [sourceWindowCoefficient_eq_zero_of_amplitude hN j hz ξ, norm_zero]
    positivity
  have hfloor := sourceWindowScale_lower_of_nonzero hN j hsupp hz
  have hinv := sourceWindowScale_inv_sqrt_cube_le hN j hfloor
  by_cases hs1 : 1 ≤ s
  · have hsp : 0 < s := by linarith
    have hraw := sourceWindowCoefficient_norm_le_normalized_gap hN hC hs1 ha j ξ
      hsep hbound0 hbound1 hbound2
    have htail : ‖triangularKernelCoefficient N (oscillatoryKernel 1 a) sourceTriangleCutoff j ξ‖ ≤
        130560 * C / s ^ 2 := by
      apply hraw.trans
      calc
        _ = (255 * C * (1 / Real.sqrt (sourceWindowScale N j) ^ 3)) / s ^ 2 := by ring
        _ ≤ (255 * C * 512) / s ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinv (by positivity)) (sq_nonneg s)
        _ = _ := by ring
    apply htail.trans
    apply (div_le_div_iff₀ (pow_pos hsp 2) hden).mpr
    have hsquare : (1 + s) ^ 2 ≤ 4 * s ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 130560 * C)]
  · have hsmall : s < 1 := lt_of_not_ge hs1
    apply (sourceWindowCoefficient_norm_le_uniform hN hC ha j ξ hbound0 hbound1).trans
    apply (le_div_iff₀ hden).mpr
    have hsquare : (1 + s) ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 52 * C)]

/-- The original weighted derivative assumptions give a uniform constant for
every actual window and every nonnegative pointwise gap. The constant precedes
all amplitudes, frequencies, scales and window indices. -/
theorem exists_sourceWindowCoefficient_smoothed_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ A0 : ℝ, 0 ≤ A0 → ∀ a : ℝ → ℂ, ContDiff ℝ ∞ a →
      (∀ u > 0, ‖a u‖ ≤ A0 * u ^ (-3 / 4 : ℝ)) →
      (∀ u > 0, ‖deriv a u‖ ≤ A0 * u ^ (-3 / 4 - 1 : ℝ)) →
      (∀ u > 0, ‖deriv (deriv a) u‖ ≤ A0 * u ^ (-3 / 4 - 2 : ℝ)) →
      ∀ N : ℝ, 0 < N →
      (∀ u : ℝ, 4 * N ^ (4 / 3 : ℝ) < u → a u = 0) →
      ∀ (j : ℕ) (ξ s : ℝ), 0 ≤ s →
      (∀ w ∈ Icc (1 / 2 : ℝ) (7 / 2),
        sourceWindowScale N j * s ≤ |sourceOscillatoryPhaseDeriv N j ξ w|) →
      ‖triangularKernelCoefficient N (oscillatoryKernel 1 a) sourceTriangleCutoff j ξ‖ ≤
        K * A0 / (1 + s) ^ 2 := by
  obtain ⟨D, hD, hDb⟩ := exists_sourceWindowAmplitude_weighted_bound
  have hDp : 0 < D := by linarith
  refine ⟨20889600 * D, by positivity, ?_⟩
  intro A0 hA0 a ha h0 h1 h2 N hN hsupp j ξ s hs hsep
  have hb (w : ℝ) (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :=
    hDb A0 hA0 a ha h0 h1 h2 N hN j w hw
  have h := sourceWindowCoefficient_norm_le_smoothed_gap hN
    (by positivity : 0 ≤ 40 * D * A0) hs ha j ξ hsupp hsep
    (fun w hw => (hb w hw).1) (fun w hw => (hb w hw).2.1)
    (fun w hw => (hb w hw).2.2)
  convert h using 1 <;> ring

end ProofProject
