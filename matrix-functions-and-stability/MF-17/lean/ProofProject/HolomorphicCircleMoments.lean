import ProofProject.SourceMomentDefs
import Mathlib.Analysis.Complex.MeanValue

/-! Angular moments of holomorphic functions on circles inside the unit disk. -/

noncomputable section

open MeasureTheory

namespace ProofProject

lemma circleMap_zero_eq_sourceCircle (r θ : ℝ) :
    circleMap 0 r θ = (r : ℂ) * sourceCircle θ := by
  simp [circleMap, sourceCircle, mul_comm Complex.I]

/-- The unnormalized angular mean of a holomorphic function on an inner circle. -/
theorem holomorphic_radial_intervalIntegral {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    (∫ θ in -Real.pi..Real.pi, F ((r : ℂ) * sourceCircle θ)) =
      (2 * Real.pi : ℂ) * F 0 := by
  have hclosed : Metric.closedBall (0 : ℂ) |r| ⊆ Metric.ball 0 1 := by
    intro z hz
    simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
      abs_of_pos hr0] at *
    exact hz.trans_lt hr1
  have hmean := (hF.diffContOnCl_ball hclosed).circleAverage (R := r)
  rw [Real.circleAverage_eq_integral_add (-Real.pi),
    intervalIntegral.integral_comp_add_right (fun θ => F (circleMap 0 r θ))] at hmean
  have hright : 2 * Real.pi + -Real.pi = Real.pi := by ring
  simp only [zero_add, hright, circleMap_zero_eq_sourceCircle] at hmean
  have hπ : 2 * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hscaled := congrArg (fun z : ℂ => (2 * Real.pi) • z) hmean
  rw [smul_smul, mul_inv_cancel₀ hπ, one_smul] at hscaled
  simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat] using hscaled

/-- All nonnegative angular moments of a holomorphic function on an inner circle.
The zeroth moment is its center value; every positive moment vanishes. -/
theorem holomorphic_radial_moment_intervalIntegral {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    (∫ θ in -Real.pi..Real.pi,
      F ((r : ℂ) * sourceCircle θ) * sourceCircle θ ^ k) =
      if k = 0 then (2 * Real.pi : ℂ) * F 0 else 0 := by
  have hr : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hG : DifferentiableOn ℂ (fun z => F z * (z / (r : ℂ)) ^ k)
      (Metric.ball 0 1) := hF.mul ((differentiableOn_id.div_const _).pow k)
  have h := holomorphic_radial_intervalIntegral hG hr0 hr1
  simp only [mul_div_cancel_left₀ _ hr, zero_div] at h
  by_cases hk : k = 0
  · simpa [hk] using h
  · simpa [hk, zero_pow hk] using h

/-- The same moment identity for Lebesgue measure restricted to the closed
principal angular interval, as used in the source's boundary integrals. -/
theorem holomorphic_radial_moment_integral {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    (∫ θ in Set.Icc (-Real.pi) Real.pi,
      F ((r : ℂ) * sourceCircle θ) * sourceCircle θ ^ k) =
      if k = 0 then (2 * Real.pi : ℂ) * F 0 else 0 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact holomorphic_radial_moment_intervalIntegral hF hr0 hr1 k

/-- The source radial moment notation, with the hypothesis stated as analyticity
on the open unit disk. -/
theorem sourceRadialMoment_eq {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    sourceRadialMoment F r k =
      if k = 0 then (2 * Real.pi : ℂ) * F 0 else 0 :=
  holomorphic_radial_moment_integral hF.differentiableOn hr0 hr1 k

end ProofProject
