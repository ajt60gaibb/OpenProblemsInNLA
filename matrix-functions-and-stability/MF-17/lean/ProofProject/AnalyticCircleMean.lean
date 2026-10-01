import ProofProject.PolynomialPhaseMoments

/-!
# Normalized circle means of analytic functions

Holomorphicity on a closed disk of radius greater than one gives uniform
polynomial approximation on the unit circle. Polynomial character orthogonality
therefore gives the mean value at the center with respect to normalized Haar
measure, followed by the corresponding norm and boundary comparison estimates.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Topology

namespace ProofProject

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The polynomial circle mean uses Haar probability measure and has no
additional factor of `2π`. -/
theorem polynomialCircle_mean (p : Polynomial ℂ) :
    (∫ z : AddCircle (1 : ℝ), p.eval (fourier 1 z)
      ∂AddCircle.haarAddCircle) = p.eval 0 := by
  apply (starRingEnd ℂ).injective
  have h := polynomialCircle_conj_moment p 0
  simpa only [Nat.cast_zero, fourier_zero, ContinuousMap.one_apply, mul_one,
    integral_conj, Polynomial.coeff_zero_eq_eval_zero] using h

/-- Restricting a function continuous on a larger disk to the unit circle
gives a continuous function on the period-one circle. -/
theorem continuous_analyticCircle {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    Continuous (fun z : AddCircle (1 : ℝ) => f (fourier 1 z)) := by
  apply hf.continuousOn.comp_continuous (fourier 1).continuous
  intro z
  simpa only [mem_closedBall, dist_zero_right, finiteCircle_fourier_norm] using hR.le

theorem integrable_analyticCircle {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    Integrable (fun z : AddCircle (1 : ℝ) => f (fourier 1 z))
      AddCircle.haarAddCircle := by
  simpa only [integrableOn_univ] using
    (continuous_analyticCircle hR hf).continuousOn.integrableOn_compact
      (μ := AddCircle.haarAddCircle) isCompact_univ

/-- The actual normalized Haar mean of an analytic circle restriction equals
the value at its center. -/
theorem analytic_circle_mean {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    (∫ z : AddCircle (1 : ℝ), f (fourier 1 z)
      ∂AddCircle.haarAddCircle) = f 0 := by
  obtain ⟨p, hp⟩ := exists_polynomial_tendstoUniformlyOn_of_differentiableOn hR hf
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨_, continuous_analyticCircle hR hf⟩
  have hconv : Tendsto (fun N => polynomialCircleMap (p N)) atTop (𝓝 F) := by
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hp ε hε] with N hN z
    exact hN _ (le_of_eq (finiteCircle_fourier_norm 1 z))
  have hzero : Tendsto (fun N => (p N).eval 0) atTop (𝓝 (f 0)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hp ε hε] with N hN
    simpa only [dist_comm] using hN 0 (by simp)
  have hi := circleContinuous_integral_tendsto hconv
  simp only [polynomialCircleMap, ContinuousMap.coe_mk, polynomialCircle_mean] at hi
  exact tendsto_nhds_unique hi hzero

/-- The value at the center is bounded by the mean boundary norm. -/
theorem analytic_circle_norm_zero_le {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    ‖f 0‖ ≤ ∫ z : AddCircle (1 : ℝ), ‖f (fourier 1 z)‖
      ∂AddCircle.haarAddCircle := by
  rw [← analytic_circle_mean hR hf]
  exact norm_integral_le_integral_norm _

/-- A pointwise polynomial square majorant controls the value at the center.
The boundary assumption itself suffices; no sign assumption on `C` is needed. -/
theorem analytic_circle_norm_zero_le_of_boundary {f : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (hf : DifferentiableOn ℂ f (closedBall 0 R))
    (p : Polynomial ℂ) (C : ℝ)
    (hbd : ∀ z : ℂ, ‖z‖ = 1 → ‖f z‖ ≤ C * ‖p.eval z‖ ^ 2) :
    ‖f 0‖ ≤ C * (∫ z : AddCircle (1 : ℝ), ‖p.eval (fourier 1 z)‖ ^ 2
      ∂AddCircle.haarAddCircle) := by
  have hp : Integrable (fun z : AddCircle (1 : ℝ) => ‖p.eval (fourier 1 z)‖ ^ 2)
      AddCircle.haarAddCircle := by
    simpa only [integrableOn_univ, Function.comp_def] using!
      ((p.continuous.comp (fourier 1).continuous).norm.fun_pow 2).continuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle) isCompact_univ
  calc
    ‖f 0‖ ≤ ∫ z : AddCircle (1 : ℝ), ‖f (fourier 1 z)‖
        ∂AddCircle.haarAddCircle := analytic_circle_norm_zero_le hR hf
    _ ≤ ∫ z : AddCircle (1 : ℝ), C * ‖p.eval (fourier 1 z)‖ ^ 2
        ∂AddCircle.haarAddCircle :=
      integral_mono (integrable_analyticCircle hR hf).norm (hp.const_mul C)
        (fun z => hbd _ (finiteCircle_fourier_norm 1 z))
    _ = _ := integral_const_mul _ _

end ProofProject
