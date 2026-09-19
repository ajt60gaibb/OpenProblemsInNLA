/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Exact planar algebra for the finite-crossing implementation of Matthew J.
Colbrook's NR-04 proof, University of Cambridge. These helpers do not assert
a supplied cyclic order or any section vertex bound. No numerical oracle or
permutation enumeration is used.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.NR04

/-- The actual two-coordinate determinant. -/
def planeDet (p q : Fin 2 → ℝ) : ℝ := p 0 * q 1 - p 1 * q 0

/-- The actual slope, used geometrically only under a positive first coordinate. -/
def planeSlope (p : Fin 2 → ℝ) : ℝ := p 1 / p 0

/-- The signed determinant of two actual displacement vectors. -/
def planeOrientation (p q r : Fin 2 → ℝ) : ℝ := planeDet (q - p) (r - p)

lemma plane_det_self (p : Fin 2 → ℝ) : planeDet p p = 0 := by
  unfold planeDet
  ring

lemma plane_det_swap (p q : Fin 2 → ℝ) : planeDet q p = -planeDet p q := by
  unfold planeDet
  ring

lemma plane_orientation_zero (q r : Fin 2 → ℝ) :
    planeOrientation 0 q r = planeDet q r := by
  simp only [planeOrientation, sub_zero]

lemma plane_det_pos_of_slope_lt (p q : Fin 2 → ℝ)
    (hp : 0 < p 0) (hq : 0 < q 0)
    (hs : planeSlope p < planeSlope q) : 0 < planeDet p q := by
  change p 1 / p 0 < q 1 / q 0 at hs
  have hcross := (div_lt_div_iff₀ hp hq).mp hs
  unfold planeDet
  nlinarith only [hcross]

/-- Cramer's two-coordinate identity with an explicitly nonzero denominator. -/
lemma plane_cramer_combination (p q r : Fin 2 → ℝ)
    (hD : planeDet p r ≠ 0) :
    q = (planeDet q r / planeDet p r) • p +
      (planeDet p q / planeDet p r) • r := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  apply (eq_div_iff hD).mpr
  fin_cases i <;> dsimp [planeDet] <;> ring

lemma plane_orientation_of_combination (p q r : Fin 2 → ℝ)
    (a b : ℝ) (hq : q = a • p + b • r) :
    planeOrientation p q r = (a + b - 1) * planeDet p r := by
  rw [hq]
  simp only [planeOrientation, planeDet, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Strict slope order yields two positive Cramer coefficients and a positive
outer determinant. This lemma supplies no bound on the sum of coefficients. -/
lemma plane_positive_combination_of_ordered_slopes (p q r : Fin 2 → ℝ)
    (hp : 0 < p 0) (hq : 0 < q 0) (hr : 0 < r 0)
    (hpq : planeSlope p < planeSlope q)
    (hqr : planeSlope q < planeSlope r) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ q = a • p + b • r ∧ 0 < planeDet p r := by
  have hpr : 0 < planeDet p r :=
    plane_det_pos_of_slope_lt p r hp hr (hpq.trans hqr)
  have hqrD : 0 < planeDet q r := plane_det_pos_of_slope_lt q r hq hr hqr
  have hpqD : 0 < planeDet p q := plane_det_pos_of_slope_lt p q hp hq hpq
  exact ⟨planeDet q r / planeDet p r, planeDet p q / planeDet p r,
    div_pos hqrD hpr, div_pos hpqD hpr,
    plane_cramer_combination p q r (ne_of_gt hpr), hpr⟩

#print axioms plane_det_self
#print axioms plane_det_swap
#print axioms plane_orientation_zero
#print axioms plane_det_pos_of_slope_lt
#print axioms plane_cramer_combination
#print axioms plane_orientation_of_combination
#print axioms plane_positive_combination_of_ordered_slopes
#assert_trust kernel plane_det_self
#assert_trust kernel plane_det_swap
#assert_trust kernel plane_orientation_zero
#assert_trust kernel plane_det_pos_of_slope_lt
#assert_trust kernel plane_cramer_combination
#assert_trust kernel plane_orientation_of_combination
#assert_trust kernel plane_positive_combination_of_ordered_slopes

end NLA.NR04
