/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, George Stepaniants
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology.

The density-point derivative estimate below generalizes Mathlib's
MeasureTheory/Function/Jacobian.lean to a different codomain. Its original
proof is due to Sébastien Gouëzel; its domain-volume argument is unchanged.
-/
import NLA.TR06.LocalVolume

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal Topology Pointwise
open MeasureTheory MeasureTheory.Measure Set Function Filter Metric

namespace NLA.TR06.Area

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {s : Set E} {f : E → F}
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem approximation_norm_fderiv_sub_le {A : E →L[ℝ] F} {δ : ℝ≥0}
    (hf : ApproximatesLinearOn f A s δ) (hs : MeasurableSet s) (f' : E → E →L[ℝ] F)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) : ∀ᵐ x ∂μ.restrict s, ‖f' x - A‖₊ ≤ δ := by
  /- The conclusion will hold at the Lebesgue density points of `s` (which have full measure).
    At such a point `x`, for any `z` and any `ε > 0` one has for small `r`
    that `{x} + r • closedBall z ε` intersects `s`. At a point `y` in the intersection,
    `f y - f x` is close both to `f' x (r z)` (by differentiability) and to `A (r z)`
    (by linear approximation), so these two quantities are close, i.e., `(f' x - A) z` is small. -/
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ s, ae_restrict_mem hs]
  -- start from a Lebesgue density point `x`, belonging to `s`.
  intro x hx xs
  -- consider an arbitrary vector `z`.
  apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
  -- to show that `‖(f' x - A) z‖ ≤ δ ‖z‖`, it suffices to do it up to some error that vanishes
  -- asymptotically in terms of `ε > 0`.
  suffices H : ∀ ε, 0 < ε → ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
    have :
      Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
        (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
      Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
    simp only [add_zero, mul_zero] at this
    apply le_of_tendsto_of_tendsto tendsto_const_nhds this
    filter_upwards [self_mem_nhdsWithin]
    exact H
  -- fix a positive `ε`.
  intro ε εpos
  -- for small enough `r`, the rescaled ball `r • closedBall z ε` intersects `s`, as `x` is a
  -- density point
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one μ s x hx _ measurableSet_closedBall
      (measure_closedBall_pos μ z εpos).ne'
  obtain ⟨ρ, ρpos, hρ⟩ :
    ∃ ρ > 0, ball x ρ ∩ s ⊆ {y : E | ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.def εpos)
  -- for small enough `r`, the rescaled ball `r • closedBall z ε` is included in the set where
  -- `f y - f x` is well approximated by `f' x (y - x)`.
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
  -- fix a small positive `r` satisfying the above properties, as well as a corresponding `y`.
  obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
    ∃ r : ℝ,
      (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧ {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  -- write `y = x + r a` with `a ∈ closedBall z ε`.
  obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, az, ha⟩
    exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
  have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
    calc
      ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
      _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
  -- use the approximation properties to control `(f' x - A) a`, and then `(f' x - A) z` as `z` is
  -- close to `a`.
  have I : r * ‖(f' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
    calc
      r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
        simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
      _ = ‖f y - f x - A (y - x) - (f y - f x - (f' x) (y - x))‖ := by
        simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
          Pi.sub_apply, map_smul, smul_sub]
      _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (f' x) (y - x)‖ := norm_sub_le _ _
      _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
      _ = r * (δ + ε) * ‖a‖ := by
        simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        ring
      _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
  calc
    ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
      congr 1
      simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
      abel
    _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
      apply add_le_add
      · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
      · apply ContinuousLinearMap.le_opNorm
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
      rw [mem_closedBall_iff_norm'] at az
      gcongr


#print axioms approximation_norm_fderiv_sub_le
#assert_trust kernel approximation_norm_fderiv_sub_le

end NLA.TR06.Area
