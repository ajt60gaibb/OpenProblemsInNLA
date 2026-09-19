/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root.

The unchanged frozen C12 contract in Sidney Holden's MI27 solution.
Ordinary matrix entropy is retained. The internally proved C11 representation
and separate finite-mixture cutoffs are imported, never assumed as hypotheses.
Frenkel, Hirche--Tomamichel, and all imported library authors retain credit.
The exact final header and helper statements passed two pre-body reviews.
-/
import NLA.MI27.MixtureRelativeEntropy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open MeasureTheory
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

theorem weighted_entropy_finite_kernel {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (R : ℝ) (hR : 1 ≤ R)
    (hρσ : ρ ≤ (R : ℂ) • σ) (hσρ : σ ≤ (R : ℂ) • ρ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    IntervalIntegrable
      (fun γ : ℝ => kernelAB a b γ * E γ ρ σ + kernelBA a b γ * E γ σ ρ)
      MeasureTheory.volume 1 R ∧
      chi a b ρ σ = ∫ γ in (1 : ℝ)..R,
        kernelAB a b γ * E γ ρ σ + kernelBA a b γ * E γ σ ρ := by
  have hfirst := c12_relative_entropy_mixture_finite hn ρ σ hρ hσ R hR hρσ hσρ
    a b ha hb hab
  have hsecond := c12_relative_entropy_mixture_finite hn σ ρ hσ hρ R hR hσρ hρσ
    b a hb ha (by linarith)
  have hswap : (b : ℂ) • σ + (a : ℂ) • ρ = (a : ℂ) • ρ + (b : ℂ) • σ := add_comm _ _
  rw [hswap] at hsecond
  let F : ℝ → ℝ := fun γ => b ^ 2 * E γ ρ σ / (γ * (b + a * γ) ^ 2) +
    b ^ 2 * E γ σ ρ / (a + b * γ) ^ 2
  let G : ℝ → ℝ := fun γ => a ^ 2 * E γ σ ρ / (γ * (a + b * γ) ^ 2) +
    a ^ 2 * E γ ρ σ / (b + a * γ) ^ 2
  have hFi : IntervalIntegrable F volume 1 R := hfirst.1
  have hGi : IntervalIntegrable G volume 1 R := hsecond.1
  have hp (v : ℝ) (hv : 1 ≤ v) : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hd1 (v : ℝ) (hv : 1 ≤ v) : 0 < b + a * v := add_pos hb (mul_pos ha (hp v hv))
  have hd2 (v : ℝ) (hv : 1 ≤ v) : 0 < a + b * v := add_pos ha (mul_pos hb (hp v hv))
  have hcoeff (v : ℝ) (hv : 1 ≤ v) :
      a * F v + b * G v = kernelAB a b v * E v ρ σ + kernelBA a b v * E v σ ρ := by
    dsimp only [F, G, kernelAB, kernelBA]
    field_simp [(hp v hv).ne', (hd1 v hv).ne', (hd2 v hv).ne']
    <;> ring
  have hE1 : ContinuousOn (fun v : ℝ => E v ρ σ) (Set.Icc 1 R) :=
    (hockey_stick_continuous_gamma hn ρ σ hρ.1.isHermitian hσ.1.isHermitian).continuousOn
  have hE2 : ContinuousOn (fun v : ℝ => E v σ ρ) (Set.Icc 1 R) :=
    (hockey_stick_continuous_gamma hn σ ρ hσ.1.isHermitian hρ.1.isHermitian).continuousOn
  have hk1 : ContinuousOn (kernelAB a b) (Set.Icc (1 : ℝ) R) :=
    continuousOn_const.div
      (continuousOn_id.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id)))
      (fun v hv => mul_ne_zero (hp v hv.1).ne' (hd1 v hv.1).ne')
  have hk2 : ContinuousOn (kernelBA a b) (Set.Icc (1 : ℝ) R) :=
    continuousOn_const.div
      (continuousOn_id.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id)))
      (fun v hv => mul_ne_zero (hp v hv.1).ne' (hd2 v hv.1).ne')
  refine ⟨((hk1.mul hE1).add (hk2.mul hE2)).intervalIntegrable_of_Icc hR, ?_⟩
  calc
    chi a b ρ σ = a * relEntropy ρ ((a : ℂ) • ρ + (b : ℂ) • σ) +
        b * relEntropy σ ((a : ℂ) • ρ + (b : ℂ) • σ) :=
      c12_chi_relative_entropy ρ σ a b
    _ = a * (∫ v in (1 : ℝ)..R, F v) + b * (∫ v in (1 : ℝ)..R, G v) := by
      rw [hfirst.2, hsecond.2]
    _ = ∫ v in (1 : ℝ)..R, a * F v + b * G v := by
      rw [intervalIntegral.integral_add (hFi.const_mul a) (hGi.const_mul b),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = _ := intervalIntegral.integral_congr (fun v hv => hcoeff v (Set.uIcc_of_le hR ▸ hv).1)

#print axioms weighted_entropy_finite_kernel
#assert_trust kernel weighted_entropy_finite_kernel

end NLA.MI27
