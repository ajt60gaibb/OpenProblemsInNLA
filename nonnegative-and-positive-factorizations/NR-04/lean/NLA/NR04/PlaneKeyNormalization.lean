/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Constructed finite order-key data for the planar implementation of Matthew J.
Colbrook's NR-04 argument, University of Cambridge. The original finite hull,
its actual affine image, and every extreme-point predicate remain explicit.
-/
import NLA.NR04.PlaneOrderKey

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

/-- From the actual finite extreme family, construct the affine normalization,
its full convex-hull image, and an injective WithBot key whose increasing
triples have positive actual orientation. No order is supplied as a premise. -/
theorem finite_extreme_family_key_order {n : ℕ}
    (w : Fin n → Fin 2 → ℝ) (hw : Function.Injective w) (hn : 0 < n)
    (hext : ∀ i, w i ∈ (convexHull ℝ (Set.range w)).extremePoints ℝ) :
    ∃ t : ℝ, ∃ i0 : Fin n,
      let f := planeShearShift t (w i0)
      let z := fun i => f (w i)
      Function.Injective f ∧ z i0 = 0 ∧ Function.Injective z ∧
      f '' convexHull ℝ (Set.range w) = convexHull ℝ (Set.range z) ∧
      (∀ i, i ≠ i0 → 0 < z i 0) ∧
      (∀ i, z i ∈ (convexHull ℝ (Set.range z)).extremePoints ℝ) ∧
      Function.Injective (planeOrderKey z i0) ∧
      (∀ i j k, planeOrderKey z i0 i < planeOrderKey z i0 j →
        planeOrderKey z i0 j < planeOrderKey z i0 k →
        0 < planeOrientation (z i) (z j) (z k)) := by
  obtain ⟨t, i0, hzero, hzinj, hpos, hextz, hslopes⟩ :=
    finite_extreme_family_positive_normalization w hw hn hext
  let f := planeShearShift t (w i0)
  let z : Fin n → Fin 2 → ℝ := fun i => f (w i)
  have hzr : f '' Set.range w = Set.range z := by
    ext y
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨w i, Set.mem_range_self i, rfl⟩
  have hhull : f '' convexHull ℝ (Set.range w) = convexHull ℝ (Set.range z) := by
    rw [f.image_convexHull, hzr]
  have hkey : Function.Injective (planeOrderKey z i0) :=
    plane_order_key_injective z i0 hslopes
  have horient : ∀ i j k, planeOrderKey z i0 i < planeOrderKey z i0 j →
      planeOrderKey z i0 j < planeOrderKey z i0 k →
      0 < planeOrientation (z i) (z j) (z k) := by
    intro i j k hij hjk
    exact plane_order_key_triple_positive z i0 hzero hextz hpos i j k hij hjk
  exact ⟨t, i0, plane_shear_shift_injective t (w i0), hzero, hzinj,
    hhull, hpos, hextz, hkey, horient⟩

#print axioms finite_extreme_family_key_order
#assert_trust kernel finite_extreme_family_key_order

end NLA.NR04
