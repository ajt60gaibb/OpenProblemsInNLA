/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

The actual planar nine-grid obstruction in the implementation of Matthew J.
Colbrook's NR-04 argument, University of Cambridge. A finite-type equivalence
feeds the original points to the proved normalization; no order is assumed.
-/
import NLA.NR04.NineGridKeyObstruction
import NLA.NR04.PlaneKeyNormalization
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

theorem nine_grid_not_all_extreme
    (w : Fin 3 × Fin 3 → Fin 2 → ℝ) (hw : Function.Injective w)
    (hcross : ∀ i k j l : Fin 3, i < k → j < l →
      (openSegment ℝ (w (i, j)) (w (k, l)) ∩
        openSegment ℝ (w (i, l)) (w (k, j))).Nonempty) :
    ¬ (∀ a, w a ∈ (convexHull ℝ (Set.range w)).extremePoints ℝ) := by
  intro hext
  let e : (Fin 3 × Fin 3) ≃ Fin (Fintype.card (Fin 3 × Fin 3)) :=
    Fintype.equivFin (Fin 3 × Fin 3)
  let u : Fin (Fintype.card (Fin 3 × Fin 3)) → Fin 2 → ℝ := fun i => w (e.symm i)
  have hu : Function.Injective u := hw.comp e.symm.injective
  have hn : 0 < Fintype.card (Fin 3 × Fin 3) := Fintype.card_pos
  have hru : Set.range u = Set.range w := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨e a, ?_⟩
      dsimp [u]
      rw [e.symm_apply_apply]
  have hextu : ∀ i, u i ∈ (convexHull ℝ (Set.range u)).extremePoints ℝ := by
    intro i
    rw [hru]
    exact hext (e.symm i)
  obtain ⟨t, i0, hf, _, _, _, _, _, hkey, hor⟩ :=
    finite_extreme_family_key_order u hu hn hextu
  let f := planeShearShift t (u i0)
  let z : Fin (Fintype.card (Fin 3 × Fin 3)) → Fin 2 → ℝ := fun i => f (u i)
  let v : Fin 3 × Fin 3 → Fin 2 → ℝ := fun a => f (w a)
  let key : Fin 3 × Fin 3 → WithBot ℝ := fun a => planeOrderKey z i0 (e a)
  have hz (a : Fin 3 × Fin 3) : z (e a) = v a := by
    dsimp [z, v, u]
    rw [e.symm_apply_apply]
  have hkey' : Function.Injective key := hkey.comp e.injective
  have hor' : ∀ a b c, key a < key b → key b < key c →
      0 < planeOrientation (v a) (v b) (v c) := by
    intro a b c hab hbc
    have hp := hor (e a) (e b) (e c) hab hbc
    change 0 < planeOrientation (z (e a)) (z (e b)) (z (e c)) at hp
    simpa only [hz] using hp
  have hcross' : ∀ i k j l : Fin 3, i < k → j < l →
      (openSegment ℝ (v (i, j)) (v (k, l)) ∩
        openSegment ℝ (v (i, l)) (v (k, j))).Nonempty := by
    intro i k j l hik hjl
    exact (affine_injective_open_crossing_iff f hf
      (w (i, j)) (w (k, l)) (w (i, l)) (w (k, j))).mp (hcross i k j l hik hjl)
  exact nine_grid_key_crossings_impossible v key hkey' hor' hcross'

#print axioms nine_grid_not_all_extreme
#assert_trust kernel nine_grid_not_all_extreme

end NLA.NR04
