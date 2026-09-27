import NLA.FR05.Gaussian.GaussianProjection
import NLA.FR05.SmallBall.GaussianSmallBall

/-!
# Gaussian projection small-ball bounds

The sections develop `GaussianProjectionSmallBall`, `GaussianProjectionUniformSmallBall`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section GaussianProjectionSmallBall

/-
Small-ball estimate for a projection under the actual complex-Gaussian tail
law.  This combines the exact law in `GaussianProjection.lean` with the
one-dimensional density estimate in `GaussianSmallBall.lean`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem signalEnergy_nonneg {n : ℕ} (z : Signal n) : 0 ≤ signalEnergy z := by
  unfold signalEnergy squaredEuclideanNorm
  exact Finset.sum_nonneg fun j hj ↦ Complex.normSq_nonneg (z j)

/-- If the real projection has variance at least `t²`, its interval
probability under the exact standard complex-Gaussian tail law is bounded by
the peak-density estimate. -/
theorem standardComplexGaussianTail_smallBall
    {n : ℕ} (z : Signal n) (a u t : ℝ)
    (hu : 0 ≤ u) (ht : 0 < t)
    (hvariance : t ^ 2 ≤ signalEnergy z / 2) :
    standardComplexGaussianTail n
        {w | |(star w ⬝ᵥ z).re - a| ≤ u} ≤
      ENNReal.ofReal (2 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  let f : Signal n → ℝ := fun w ↦ (star w ⬝ᵥ z).re
  have hnonneg : 0 ≤ signalEnergy z / 2 := div_nonneg (signalEnergy_nonneg z) (by norm_num)
  have hvar : t ^ 2 ≤ ((signalEnergy z / 2).toNNReal : ℝ) := by
    simpa only [Real.coe_toNNReal _ hnonneg] using hvariance
  have hv : (signalEnergy z / 2).toNNReal ≠ 0 := by
    intro hzero
    rw [hzero, NNReal.coe_zero] at hvar
    exact (sq_pos_of_pos ht).not_ge hvar
  have hevent : {w : Signal n | |f w - a| ≤ u} = f ⁻¹' Icc (a - u) (a + u) := by
    rw [← Real.closedBall_eq_Icc]
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq]
  change standardComplexGaussianTail n {w | |f w - a| ≤ u} ≤ _
  rw [hevent, (measurePreserving_real_star_dotProduct z).measure_preimage
    measurableSet_Icc.nullMeasurableSet]
  exact gaussianReal_Icc_smallBall_of_sq_le 0 a u t hv hu ht hvar

/-- The same interval estimate after a deterministic phase rotation of the
tail.  The rotation is transferred to the direction, where energy is
preserved, rather than appealing to an unproved invariance assertion. -/
theorem standardComplexGaussianTail_phaseRotate_smallBall
    {n : ℕ} (α : ℝ) (z : Signal n) (a u t : ℝ)
    (hu : 0 ≤ u) (ht : 0 < t)
    (hvariance : t ^ 2 ≤ signalEnergy z / 2) :
    standardComplexGaussianTail n
        {w | |(star (Complex.exp ((-α : ℂ) * Complex.I) • w) ⬝ᵥ z).re - a| ≤ u} ≤
      ENNReal.ofReal (2 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  simp_rw [phaseRotate_real_dotProduct]
  apply standardComplexGaussianTail_smallBall _ a u t hu ht
  simpa only [signalEnergy_phaseRotate] using hvariance

end GaussianProjectionSmallBall

section GaussianProjectionUniformSmallBall

/-
Variance-uniform small-ball bound for an actual complex-Gaussian projection.

This transfers the scalar estimate from `GaussianSmallBall` through
the exact pushforward identity for `standardComplexGaussianTail`; no positive
lower bound on the projection variance is required.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Away from the deterministic centre, the small-ball probability for the
real part of an actual standard complex-Gaussian projection is uniformly
bounded over all directions, including the zero direction. -/
theorem standardComplexGaussianTail_real_dotProduct_abs_add_smallBall_uniform
    {n : ℕ} (z : Signal n) (m u t : ℝ)
    (ht : 0 < t) (hcentre : t ≤ |m|) (hscale : 2 * u ≤ t) :
    standardComplexGaussianTail n
        {w : Signal n | |m + (star w ⬝ᵥ z).re| ≤ u} ≤
      ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  have hs : MeasurableSet {x : ℝ | |m + x| ≤ u} := by
    exact (isClosed_le (continuous_const.add continuous_id).abs continuous_const).measurableSet
  change standardComplexGaussianTail n
    ((fun w : Signal n ↦ (star w ⬝ᵥ z).re) ⁻¹' {x : ℝ | |m + x| ≤ u}) ≤ _
  rw [(measurePreserving_real_star_dotProduct z).measure_preimage hs.nullMeasurableSet]
  exact gaussianReal_abs_add_smallBall_uniform m u t ht hcentre hscale

end GaussianProjectionUniformSmallBall

end NLA.FR05
