/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Only the fixed scalar exp(-2) needs a numerical certificate. Monotonicity
extends this one kernel-checked point inequality to the full Gaussian interval;
there is no dimension-dependent interval subdivision or numerical integration.
-/
import NLA.IE04.Definitions
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section
namespace NLA.IE04

theorem exp_neg_two_lower : (1 / 8 : ℝ) < Real.exp (-2) := by
  interval_decide 12 (trust := kernel)

theorem standard_normal_density_lower (z : ℝ) (hz : |z| ≤ 2) :
    (1 / 32 : ℝ) < gaussianPDFReal 0 1 z := by
  have hsq : z ^ 2 ≤ 4 := by
    have hmul := mul_le_mul hz hz (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [sq_abs z]
  have harg : (-2 : ℝ) ≤ -z ^ 2 / 2 := by linarith
  have hexp : (1 / 8 : ℝ) < Real.exp (-z ^ 2 / 2) :=
    exp_neg_two_lower.trans_le (Real.exp_le_exp.mpr harg)
  have hspos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hslt : Real.sqrt (2 * Real.pi) < 3 :=
    (Real.sqrt_lt (by positivity) (by norm_num)).mpr (by nlinarith [Real.pi_lt_four])
  have hquot : (1 / 32 : ℝ) < Real.exp (-z ^ 2 / 2) / Real.sqrt (2 * Real.pi) :=
    (lt_div_iff₀ hspos).mpr (by nlinarith)
  simpa only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, div_eq_mul_inv,
    mul_comm] using hquot

theorem gaussian_interval_lower (a δ : ℝ) (ha : |a| ≤ 1)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) :
    ENNReal.ofReal (δ / 16) ≤ gaussianReal 0 1 (Set.Icc (a - δ) (a + δ)) := by
  have hpoint : ∀ z ∈ Set.Icc (a - δ) (a + δ),
      ENNReal.ofReal (1 / 32 : ℝ) ≤ gaussianPDF 0 1 z := by
    intro z hz
    have ha' := abs_le.mp ha
    have habs : |z| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2]
    exact ENNReal.ofReal_le_ofReal (standard_normal_density_lower z habs).le
  rw [gaussianReal_apply 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  calc
    ENNReal.ofReal (δ / 16) = ENNReal.ofReal (1 / 32 : ℝ) *
        volume (Set.Icc (a - δ) (a + δ)) := by
      rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 32)]
      congr 1
      ring
    _ = ∫⁻ _ in Set.Icc (a - δ) (a + δ), ENNReal.ofReal (1 / 32 : ℝ) :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ z in Set.Icc (a - δ) (a + δ), gaussianPDF 0 1 z :=
      setLIntegral_mono (measurable_gaussianPDF 0 1) hpoint

#assert_trust kernel exp_neg_two_lower
#print axioms exp_neg_two_lower
#assert_trust kernel standard_normal_density_lower
#print axioms standard_normal_density_lower
#assert_trust kernel gaussian_interval_lower
#print axioms gaussian_interval_lower

end NLA.IE04
