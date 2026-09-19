/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Actual crossing orientation in the planar implementation of Matthew J.
Colbrook's NR-04 argument, University of Cambridge. These algebraic and
open-segment helpers do not assume a polygon order or final vertex bound.
-/
import NLA.NR04.PlaneDeterminants
import Mathlib.Analysis.Convex.Segment

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

lemma plane_orientation_cyclic (a b c : Fin 2 → ℝ) :
    planeOrientation a b c = planeOrientation b c a := by
  simp only [planeOrientation, planeDet, Pi.sub_apply]
  ring

lemma plane_orientation_swap_first (a b c : Fin 2 → ℝ) :
    planeOrientation b a c = -planeOrientation a b c := by
  simp only [planeOrientation, planeDet, Pi.sub_apply]
  ring

lemma plane_orientation_swap_last (a b c : Fin 2 → ℝ) :
    planeOrientation a c b = -planeOrientation a b c := by
  simp only [planeOrientation, planeDet, Pi.sub_apply]
  ring

lemma plane_orientation_left_eq_zero (a b : Fin 2 → ℝ) :
    planeOrientation a b a = 0 := by
  simp [planeOrientation, planeDet]

lemma plane_orientation_right_eq_zero (a b : Fin 2 → ℝ) :
    planeOrientation a b b = 0 := by
  exact plane_det_self (b - a)

lemma plane_orientation_affine_combination (a b c d : Fin 2 → ℝ)
    (s t : ℝ) (hst : s + t = 1) :
    planeOrientation a b (s • c + t • d) =
      s * planeOrientation a b c + t * planeOrientation a b d := by
  have ht : t = 1 - s := by linarith only [hst]
  rw [ht]
  simp only [planeOrientation, planeDet, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

lemma plane_orientation_on_open_segment (a b p : Fin 2 → ℝ)
    (hp : p ∈ openSegment ℝ a b) : planeOrientation a b p = 0 := by
  obtain ⟨s, t, _, _, hst, hp⟩ := hp
  rw [← hp, plane_orientation_affine_combination a b a b s t hst,
    plane_orientation_left_eq_zero, plane_orientation_right_eq_zero]
  ring

/-- The actual affine orientation functional at an actual open-segment
intersection forces opposite endpoint signs. -/
lemma crossing_orientation_opposite (a b c d : Fin 2 → ℝ)
    (hcross : (openSegment ℝ a b ∩ openSegment ℝ c d).Nonempty)
    (hc : planeOrientation a b c ≠ 0) :
    (planeOrientation a b c < 0 ∧ 0 < planeOrientation a b d) ∨
      (0 < planeOrientation a b c ∧ planeOrientation a b d < 0) := by
  obtain ⟨p, hpab, hpcd⟩ := hcross
  have hpzero := plane_orientation_on_open_segment a b p hpab
  obtain ⟨s, t, hs, ht, hst, hp⟩ := hpcd
  have hweighted : s * planeOrientation a b c + t * planeOrientation a b d = 0 := by
    rw [← plane_orientation_affine_combination a b c d s t hst, hp]
    exact hpzero
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · refine Or.inl ⟨hcneg, ?_⟩
    have hcprod : s * planeOrientation a b c < 0 := mul_neg_of_pos_of_neg hs hcneg
    have hdprod : 0 < t * planeOrientation a b d := by
      linarith only [hweighted, hcprod]
    exact (mul_pos_iff_of_pos_left ht).mp hdprod
  · refine Or.inr ⟨hcpos, ?_⟩
    have hcprod : 0 < s * planeOrientation a b c := mul_pos hs hcpos
    have hdprod : t * planeOrientation a b d < 0 := by
      linarith only [hweighted, hcprod]
    by_contra hdn
    have hdnonneg : 0 ≤ planeOrientation a b d := le_of_not_gt hdn
    have hdnprod : 0 ≤ t * planeOrientation a b d := mul_nonneg ht.le hdnonneg
    linarith only [hdprod, hdnprod]

#print axioms plane_orientation_cyclic
#print axioms plane_orientation_swap_first
#print axioms plane_orientation_swap_last
#print axioms plane_orientation_left_eq_zero
#print axioms plane_orientation_right_eq_zero
#print axioms plane_orientation_affine_combination
#print axioms plane_orientation_on_open_segment
#print axioms crossing_orientation_opposite
#assert_trust kernel plane_orientation_cyclic
#assert_trust kernel plane_orientation_swap_first
#assert_trust kernel plane_orientation_swap_last
#assert_trust kernel plane_orientation_left_eq_zero
#assert_trust kernel plane_orientation_right_eq_zero
#assert_trust kernel plane_orientation_affine_combination
#assert_trust kernel plane_orientation_on_open_segment
#assert_trust kernel crossing_orientation_opposite

end NLA.NR04
