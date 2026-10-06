/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import NLA.IE06.Vendor.SLT.GaussianPoincare.Limit
import NLA.IE06.Vendor.SLT.GaussianLSI.BernoulliLSI
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"

/-!
# 1-Dimensional Gaussian Log-Sobolev Inequality

This file proves the 1-dimensional Gaussian log-Sobolev inequality for compactly
supported smooth functions by taking the limit of the Bernoulli log-Sobolev inequality.

## Main results

* `gaussian_logSobolev_CompSmo`: For `f ∈ C_c²(ℝ)` and `X ~ N(0,1)`:
  `Ent_μ(f²) ≤ 2 · E[f'(X)²]`

## Proof strategy

We pass n → ∞ in the Bernoulli log-Sobolev inequality:
  `Ent_{S_{n+1}}(f²) ≤ (1/2) · ∑ᵢ E[(f(S_{n+1}) - f(S_{n+1} with coord i flipped))²]`

By the CLT, the law of `S_{n+1}` converges weakly to `N(0,1)`. We have:
- `tendsto_entropy_f_sq`: The LHS converges to `Ent_{N(0,1)}(f²)`
- `tendsto_sum_sq_shifted_four_deriv_sq`: The RHS sum converges to `4 · E[f'(X)²]`

Taking the limit of the inequality yields:
  `Ent_{N(0,1)}(f²) ≤ (1/2) · 4 · E[f'(X)²] = 2 · E[f'(X)²]`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter Set Function Topology
open scoped ENNReal Topology

open EfronSteinApp GaussianPoincare BernoulliLSI

namespace GaussianLSI

/-- **1-Dimensional Gaussian Log-Sobolev Inequality for Compactly Supported Smooth Functions**

For f ∈ C_c²(ℝ) (compactly supported, twice continuously differentiable), the entropy
of f² under the standard Gaussian measure is bounded by twice the expected squared derivative:

  Ent_{N(0,1)}(f²) ≤ 2 · E[f'(X)²]

where Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log(∫ g dμ). -/
theorem gaussian_logSobolev_CompSmo {f : ℝ → ℝ} (hf : CompactlySupportedSmooth f) :
    LogSobolev.entropy stdGaussianMeasure (fun x => (f x)^2) ≤
    2 * ∫ x, (deriv f x)^2 ∂stdGaussianMeasure := by
  -- Step 1: Establish convergence of the LHS (entropy)
  have h_lhs : Tendsto (fun n => LogSobolev.entropy (rademacherLaw (n + 1)).toMeasure
      (fun x => (f x)^2)) atTop (𝓝 (LogSobolev.entropy stdGaussianMeasure (fun x => (f x)^2))) :=
    tendsto_entropy_f_sq hf
  -- Step 2: Establish convergence of the RHS (gradient sum → 4 * ∫ (deriv f)²)
  have h_sum : Tendsto (fun n => ∑ i : Fin (n + 1), ∫ x,
      (f (rademacherSumProd (n + 1) x) - f (rademacherSumShifted (n + 1) i x))^2
        ∂rademacherProductMeasure (n + 1)) atTop
      (𝓝 (4 * ∫ x, (deriv f x)^2 ∂stdGaussianMeasure)) :=
    tendsto_sum_sq_shifted_four_deriv_sq hf
  -- Step 3: The RHS of the discrete inequality converges to (1/2) * 4 * ∫ (deriv f)² = 2 * ∫ (deriv f)²
  have h_rhs : Tendsto (fun n => (1/2 : ℝ) * ∑ i : Fin (n + 1), ∫ x,
      (f (rademacherSumProd (n + 1) x) - f (rademacherSumShifted (n + 1) i x))^2
        ∂rademacherProductMeasure (n + 1)) atTop
      (𝓝 ((1/2 : ℝ) * (4 * ∫ x, (deriv f x)^2 ∂stdGaussianMeasure))) := by
    exact h_sum.const_mul (1/2 : ℝ)
  -- Simplify the limit: (1/2) * 4 = 2
  have h_rhs' : Tendsto (fun n => (1/2 : ℝ) * ∑ i : Fin (n + 1), ∫ x,
      (f (rademacherSumProd (n + 1) x) - f (rademacherSumShifted (n + 1) i x))^2
        ∂rademacherProductMeasure (n + 1)) atTop
      (𝓝 (2 * ∫ x, (deriv f x)^2 ∂stdGaussianMeasure)) := by
    convert h_rhs using 2
    ring
  -- Step 4: For each n, the Bernoulli log-Sobolev inequality holds
  have h_ineq : ∀ n : ℕ, LogSobolev.entropy (rademacherLaw (n + 1)).toMeasure (fun x => (f x)^2) ≤
      (1/2 : ℝ) * ∑ i : Fin (n + 1), ∫ x,
        (f (rademacherSumProd (n + 1) x) - f (rademacherSumShifted (n + 1) i x))^2
          ∂rademacherProductMeasure (n + 1) := fun n => bernoulli_logSobolev_app hf n
  -- Step 5: Pass the inequality to the limit
  exact le_of_tendsto_of_tendsto h_lhs h_rhs' (Eventually.of_forall h_ineq)

lemma deriv_sq_eq_norm_fderiv_sq (f : ℝ → ℝ) (x : ℝ) :
    (deriv f x)^2 = ‖fderiv ℝ f x‖^2 := by
  have hnorm : ‖deriv f x‖ = ‖fderiv ℝ f x‖ := by
    simp [norm_deriv_eq_norm_fderiv (f := f) (x := x)]
  calc
    (deriv f x)^2 = ‖deriv f x‖^2 := by
      simp [Real.norm_eq_abs, sq_abs]
    _ = ‖fderiv ℝ f x‖^2 := by
      simp [hnorm]

theorem gaussian_logSobolev_CompSmo_fderiv {f : ℝ → ℝ} (hf : CompactlySupportedSmooth f) :
    LogSobolev.entropy stdGaussianMeasure (fun x => (f x)^2) ≤
    2 * ∫ x, ‖fderiv ℝ f x‖^2 ∂stdGaussianMeasure := by
  simpa [deriv_sq_eq_norm_fderiv_sq] using (gaussian_logSobolev_CompSmo (f := f) hf)

end GaussianLSI

end
