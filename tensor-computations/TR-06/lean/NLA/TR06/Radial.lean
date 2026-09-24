/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Definitions
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace NLA.TR06

/-- The canonical range r >= 3 already implies the origin convergence threshold.
Mode-size and order hypotheses are not needed for this arithmetic bound. -/
theorem expectedDimension_gt_one {d : ℕ} (n : Fin d → ℕ) (r : ℕ) (hr : 3 ≤ r) :
    1 < expectedDimension d n r := by
  unfold expectedDimension
  have hp : 0 < 1 + ∑ j, (n j - 1) := by omega
  have hle := Nat.le_mul_of_pos_right r hp
  omega

/-- Exact analytic radial convergence, without quadrature or Gamma evaluation.
This lemma alone does not prove the angular link integral or TR-06. -/
theorem radial_integrable {d : ℕ} (n : Fin d → ℕ) (r : ℕ) (hr : 3 ≤ r) :
    IntegrableOn (fun t : ℝ => t ^ ((expectedDimension d n r : ℝ) - 2) *
      Real.exp (- (1 / 2 : ℝ) * t ^ 2)) (Ioi 0) ∧
    IntegrableOn (fun t : ℝ => t ^ ((expectedDimension d n r : ℝ) - 1) *
      Real.exp (- (1 / 2 : ℝ) * t ^ 2)) (Ioi 0) := by
  have hk : (1 : ℝ) < expectedDimension d n r := by
    exact_mod_cast expectedDimension_gt_one n r hr
  constructor
  · exact integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) (by linarith)
  · exact integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) (by linarith)

#print axioms expectedDimension_gt_one
#print axioms radial_integrable
#assert_trust kernel expectedDimension_gt_one
#assert_trust kernel radial_integrable
end NLA.TR06
