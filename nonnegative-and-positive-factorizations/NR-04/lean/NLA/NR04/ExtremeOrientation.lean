/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Actual extreme-point geometry for the finite-crossing implementation of
Matthew J. Colbrook's NR-04 proof, University of Cambridge. The origin is
an actual member of the convex set, and strict slope order is an explicit
helper premise whose construction remains a separate obligation.
-/
import NLA.NR04.PlaneDeterminants
import Mathlib.Analysis.Convex.Extreme

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NR04

/-- An actual extreme point cannot be a positive two-vector combination of
total weight at most one when the origin belongs to the convex set and the
first vector differs from the extreme point. The proof supplies the actual
open-segment witness, not an assumed separating hyperplane. -/
lemma extreme_positive_combination_weight_sum {N : ℕ}
    (S : Set (Fin N → ℝ)) (hS : Convex ℝ S)
    (h0 : (0 : Fin N → ℝ) ∈ S)
    (p q r : Fin N → ℝ) (hp : p ∈ S) (hr : r ∈ S)
    (hq : q ∈ S.extremePoints ℝ) (hpq : p ≠ q)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (heq : q = a • p + b • r) : 1 < a + b := by
  by_contra hn
  have hle : a + b ≤ 1 := le_of_not_gt hn
  have hd : 0 < 1 - a := by linarith only [hb, hle]
  have hratio : b / (1 - a) ≤ 1 :=
    (div_le_one hd).mpr (by linarith only [hle])
  let v : Fin N → ℝ := (b / (1 - a)) • r
  have hv : v ∈ S := hS.smul_mem_of_zero_mem h0 hr
    ⟨(div_pos hb hd).le, hratio⟩
  have hcancel : (1 - a) * (b / (1 - a)) = b := by
    field_simp [ne_of_gt hd] <;> ring
  have hseg : q ∈ openSegment ℝ p v := by
    refine ⟨a, 1 - a, ha, hd, by ring, ?_⟩
    calc
      a • p + (1 - a) • v = a • p + b • r := by
        dsimp [v]
        rw [smul_smul, hcancel]
      _ = q := heq.symm
  exact hpq (hq.2 hp hv hseg)

/-- With positive first coordinates and increasing slopes, actual extremality
of the middle point forces the three-point orientation to be positive. -/
lemma plane_orientation_pos_of_extreme_ordered_slopes
    (S : Set (Fin 2 → ℝ)) (hS : Convex ℝ S)
    (h0 : (0 : Fin 2 → ℝ) ∈ S)
    (p q r : Fin 2 → ℝ) (hp : p ∈ S) (hr : r ∈ S)
    (hq : q ∈ S.extremePoints ℝ)
    (hpx : 0 < p 0) (hqx : 0 < q 0) (hrx : 0 < r 0)
    (hpq : planeSlope p < planeSlope q)
    (hqr : planeSlope q < planeSlope r) :
    0 < planeOrientation p q r := by
  obtain ⟨a, b, ha, hb, hcomb, hD⟩ :=
    plane_positive_combination_of_ordered_slopes p q r hpx hqx hrx hpq hqr
  have hpqne : p ≠ q := by
    intro heq
    exact (ne_of_lt hpq) (congrArg planeSlope heq)
  have hweights : 1 < a + b :=
    extreme_positive_combination_weight_sum S hS h0 p q r hp hr hq hpqne
      a b ha hb hcomb
  rw [plane_orientation_of_combination p q r a b hcomb]
  exact mul_pos (sub_pos.mpr hweights) hD

/-- For nonorigin points sorted by actual slopes, every increasing triple
has positive orientation. The actual convex hull explicitly includes the
origin as an additional generator, so the premises are not vacuous. -/
theorem ordered_extreme_hull_triples_positive {n : ℕ}
    (w : Fin n → Fin 2 → ℝ)
    (hext : ∀ i, w i ∈
      (convexHull ℝ (insert (0 : Fin 2 → ℝ) (Set.range w))).extremePoints ℝ)
    (hx : ∀ i, 0 < w i 0)
    (hs : StrictMono (fun i => planeSlope (w i)))
    (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    0 < planeOrientation (w i) (w j) (w k) := by
  have h0 : (0 : Fin 2 → ℝ) ∈
      convexHull ℝ (insert (0 : Fin 2 → ℝ) (Set.range w)) :=
    subset_convexHull ℝ _ (by simp)
  exact plane_orientation_pos_of_extreme_ordered_slopes
    (convexHull ℝ (insert (0 : Fin 2 → ℝ) (Set.range w)))
    (convex_convexHull ℝ _) h0 (w i) (w j) (w k)
    (hext i).1 (hext k).1 (hext j) (hx i) (hx j) (hx k) (hs hij) (hs hjk)

#print axioms extreme_positive_combination_weight_sum
#print axioms plane_orientation_pos_of_extreme_ordered_slopes
#print axioms ordered_extreme_hull_triples_positive
#assert_trust kernel extreme_positive_combination_weight_sum
#assert_trust kernel plane_orientation_pos_of_extreme_ordered_slopes
#assert_trust kernel ordered_extreme_hull_triples_positive

end NLA.NR04
