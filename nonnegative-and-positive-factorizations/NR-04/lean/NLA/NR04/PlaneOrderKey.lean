/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

An actual WithBot real key for the normalized extreme family in the planar
implementation of Matthew J. Colbrook's NR-04 argument, University of Cambridge.
No cyclic order or permutation is supplied as an assumption.
-/
import NLA.NR04.ExtremeSlopes
import Mathlib.Order.WithBot

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

/-- The selected origin precedes every real slope; other keys are actual slopes. -/
def planeOrderKey {n : ℕ} (z : Fin n → Fin 2 → ℝ) (i0 i : Fin n) : WithBot ℝ :=
  if i = i0 then ⊥ else (planeSlope (z i) : WithBot ℝ)

lemma plane_order_key_center {n : ℕ} (z : Fin n → Fin 2 → ℝ) (i0 : Fin n) :
    planeOrderKey z i0 i0 = ⊥ := by
  simp [planeOrderKey]

lemma plane_order_key_center_lt {n : ℕ} (z : Fin n → Fin 2 → ℝ)
    (i0 i : Fin n) (hi : i ≠ i0) : planeOrderKey z i0 i0 < planeOrderKey z i0 i := by
  simp [planeOrderKey, hi]

lemma plane_order_key_lt_iff_of_ne {n : ℕ} (z : Fin n → Fin 2 → ℝ)
    (i0 i j : Fin n) (hi : i ≠ i0) (hj : j ≠ i0) :
    planeOrderKey z i0 i < planeOrderKey z i0 j ↔ planeSlope (z i) < planeSlope (z j) := by
  simp only [planeOrderKey, if_neg hi, if_neg hj, WithBot.coe_lt_coe]

lemma plane_order_key_injective {n : ℕ} (z : Fin n → Fin 2 → ℝ) (i0 : Fin n)
    (hs : Function.Injective
      (fun i : {i : Fin n // i ≠ i0} => planeSlope (z i.1))) :
    Function.Injective (planeOrderKey z i0) := by
  intro i j hij
  by_cases hi : i = i0
  · subst i
    by_cases hj : j = i0
    · exact hj.symm
    · simp [planeOrderKey, hj] at hij
  · by_cases hj : j = i0
    · subst j
      simp [planeOrderKey, hi] at hij
    · have hslopes : planeSlope (z i) = planeSlope (z j) := by
        simpa only [planeOrderKey, if_neg hi, if_neg hj, WithBot.coe_inj] using hij
      have hsub := @hs ⟨i, hi⟩ ⟨j, hj⟩ hslopes
      exact congrArg Subtype.val hsub

/-- Every increasing key triple has positive actual orientation. This includes
the origin case, and its two later keys are proved to be real slopes. -/
lemma plane_order_key_triple_positive {n : ℕ}
    (z : Fin n → Fin 2 → ℝ) (i0 : Fin n) (hzero : z i0 = 0)
    (hext : ∀ i, z i ∈ (convexHull ℝ (Set.range z)).extremePoints ℝ)
    (hx : ∀ i, i ≠ i0 → 0 < z i 0)
    (i j k : Fin n)
    (hij : planeOrderKey z i0 i < planeOrderKey z i0 j)
    (hjk : planeOrderKey z i0 j < planeOrderKey z i0 k) :
    0 < planeOrientation (z i) (z j) (z k) := by
  have hj : j ≠ i0 := by
    intro heq
    have hbad := hij
    rw [heq, plane_order_key_center] at hbad
    exact not_lt_bot hbad
  have hk : k ≠ i0 := by
    intro heq
    have hbad := hjk
    rw [heq, plane_order_key_center] at hbad
    exact not_lt_bot hbad
  have hsjk : planeSlope (z j) < planeSlope (z k) :=
    (plane_order_key_lt_iff_of_ne z i0 j k hj hk).mp hjk
  by_cases hi : i = i0
  · rw [hi, hzero, plane_orientation_zero]
    exact plane_det_pos_of_slope_lt (z j) (z k) (hx j hj) (hx k hk) hsjk
  · have hsij : planeSlope (z i) < planeSlope (z j) :=
      (plane_order_key_lt_iff_of_ne z i0 i j hi hj).mp hij
    have h0 : (0 : Fin 2 → ℝ) ∈ convexHull ℝ (Set.range z) := by
      rw [← hzero]
      exact subset_convexHull ℝ _ (Set.mem_range_self i0)
    exact plane_orientation_pos_of_extreme_ordered_slopes
      (convexHull ℝ (Set.range z)) (convex_convexHull ℝ _) h0
      (z i) (z j) (z k) (hext i).1 (hext k).1 (hext j)
      (hx i hi) (hx j hj) (hx k hk) hsij hsjk

#print axioms plane_order_key_center
#print axioms plane_order_key_center_lt
#print axioms plane_order_key_lt_iff_of_ne
#print axioms plane_order_key_injective
#print axioms plane_order_key_triple_positive
#assert_trust kernel plane_order_key_center
#assert_trust kernel plane_order_key_center_lt
#assert_trust kernel plane_order_key_lt_iff_of_ne
#assert_trust kernel plane_order_key_injective
#assert_trust kernel plane_order_key_triple_positive

end NLA.NR04
