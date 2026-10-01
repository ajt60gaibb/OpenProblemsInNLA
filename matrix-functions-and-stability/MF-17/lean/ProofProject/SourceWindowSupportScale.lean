import ProofProject.SourceWindowDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The scale floor for nonzero source windows

The support bound is used only after finding a point where the actual scaled
amplitude is nonzero. Windows beyond the support are handled by a separate
zero-coefficient theorem, without an invalid scale floor for all indices.
-/

noncomputable section
open MeasureTheory Set
namespace ProofProject

/-- The square-root cube of the source support scale is exactly `N²`. -/
theorem sqrt_cube_rpow_four_thirds {N : ℝ} (hN : 0 ≤ N) :
    Real.sqrt (N ^ (4 / 3 : ℝ)) ^ 3 = N ^ 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Real.rpow_nonneg hN _),
    ← Real.rpow_mul hN]
  norm_num

/-- A center lying below sixteen times the support scale has a curvature
scale at least `1/64`. -/
theorem sourceWindowScale_lower_of_center_bound {N : ℝ} (hN : 0 < N) (j : ℕ)
    (hcenter : N * ((j : ℝ) + 2) ≤ 16 * N ^ (4 / 3 : ℝ)) :
    (1 / 64 : ℝ) ≤ sourceWindowScale N j := by
  have hV : 0 < N * ((j : ℝ) + 2) := mul_pos hN (by positivity)
  have hs : 0 < Real.sqrt (N * ((j : ℝ) + 2)) := Real.sqrt_pos.mpr hV
  have hden : Real.sqrt (N * ((j : ℝ) + 2)) ^ 3 ≤ 64 * N ^ 2 := by
    calc
      _ ≤ Real.sqrt (16 * N ^ (4 / 3 : ℝ)) ^ 3 := by
        gcongr
      _ = 64 * N ^ 2 := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
        rw [mul_pow, sqrt_cube_rpow_four_thirds hN.le]
        norm_num
  unfold sourceWindowScale
  apply (le_div_iff₀ (pow_pos hs 3)).mpr
  linarith

/-- Only a nonzero actual amplitude permits use of the original kernel support
in order to bound the center scale. -/
theorem sourceWindow_center_bound_of_nonzero {N : ℝ} (hN : 0 < N)
    {a : ℝ → ℂ} (j : ℕ)
    (hsupp : ∀ u : ℝ, 4 * N ^ (4 / 3 : ℝ) < u → a u = 0)
    (hne : sourceWindowAmplitude N a j ≠ 0) :
    N * ((j : ℝ) + 2) ≤ 16 * N ^ (4 / 3 : ℝ) := by
  obtain ⟨w, hw⟩ : ∃ w, sourceWindowAmplitude N a j w ≠ 0 := by
    by_contra h
    apply hne
    funext w
    simpa using (not_exists.mp h w)
  have hwin := sourceWindowAmplitude_tsupport_subset N a j (subset_closure hw)
  have harg := (sourceWindow_argument_bounds hN j ⟨hwin.1.le, hwin.2.le⟩).1
  have ha : a (N * ((j : ℝ) + w)) ≠ 0 := by
    intro h
    simp [sourceWindowAmplitude, h] at hw
  have hupper : N * ((j : ℝ) + w) ≤ 4 * N ^ (4 / 3 : ℝ) := by
    by_contra h
    exact ha (hsupp _ (lt_of_not_ge h))
  linarith

theorem sourceWindowScale_lower_of_nonzero {N : ℝ} (hN : 0 < N)
    {a : ℝ → ℂ} (j : ℕ)
    (hsupp : ∀ u : ℝ, 4 * N ^ (4 / 3 : ℝ) < u → a u = 0)
    (hne : sourceWindowAmplitude N a j ≠ 0) :
    (1 / 64 : ℝ) ≤ sourceWindowScale N j :=
  sourceWindowScale_lower_of_center_bound hN j
    (sourceWindow_center_bound_of_nonzero hN j hsupp hne)

/-- The scale factor in the nonstationary estimate is bounded absolutely on
nonzero windows. -/
theorem sourceWindowScale_inv_sqrt_cube_le {N : ℝ} (hN : 0 < N)
    (j : ℕ) (hlower : (1 / 64 : ℝ) ≤ sourceWindowScale N j) :
    1 / Real.sqrt (sourceWindowScale N j) ^ 3 ≤ (512 : ℝ) := by
  have hL := sourceWindowScale_pos hN j
  have hs : 0 < Real.sqrt (sourceWindowScale N j) := Real.sqrt_pos.mpr hL
  have hroot : (1 / 8 : ℝ) ≤ Real.sqrt (sourceWindowScale N j) := by
    nlinarith [Real.sq_sqrt hL.le]
  have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 8) hroot 3
  apply (div_le_iff₀ (pow_pos hs 3)).mpr
  norm_num at hcube
  linarith

/-- An identically zero scaled amplitude gives zero at every frequency,
regardless of the value of the center curvature scale. -/
theorem sourceWindowCoefficient_eq_zero_of_amplitude {N : ℝ} (hN : 0 < N)
    {a : ℝ → ℂ} (j : ℕ) (hzero : sourceWindowAmplitude N a j = 0) (ξ : ℝ) :
    triangularKernelCoefficient N (oscillatoryKernel 1 a) sourceTriangleCutoff j ξ = 0 := by
  rw [sourceWindowCoefficient_eq_integral hN, hzero]
  simp

end ProofProject
