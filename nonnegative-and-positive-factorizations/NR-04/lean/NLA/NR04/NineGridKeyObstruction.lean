/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

The actual nine-grid parity contradiction in the planar implementation of
Matthew J. Colbrook's NR-04 argument, University of Cambridge. Row/column
indicators are defined from the actual constructed key, not assumed arrays.
-/
import NLA.NR04.FourEndpointCrossingParity
import NLA.NR04.RectangleParity

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

theorem nine_grid_key_crossings_impossible
    (w : Fin 3 × Fin 3 → Fin 2 → ℝ)
    (key : Fin 3 × Fin 3 → WithBot ℝ) (hkey : Function.Injective key)
    (hor : ∀ a b c, key a < key b → key b < key c →
      0 < planeOrientation (w a) (w b) (w c))
    (hcross : ∀ i k j l : Fin 3, i < k → j < l →
      (openSegment ℝ (w (i, j)) (w (k, l)) ∩
        openSegment ℝ (w (i, l)) (w (k, j))).Nonempty) : False := by
  let R : Fin 3 → Fin 3 → Fin 3 → ℤ := fun i j l => keyIndicator (key (i, j)) (key (i, l))
  let C : Fin 3 → Fin 3 → Fin 3 → ℤ := fun j i k => keyIndicator (key (i, j)) (key (k, j))
  apply nine_rectangle_parities_impossible R C
  intro i k j l hik hjl
  have hodd := four_endpoint_crossing_odd w key hkey hor
    (i, j) (k, l) (i, l) (k, j)
    (by intro h; exact (ne_of_lt hik) (congrArg Prod.fst h))
    (by intro h; exact (ne_of_lt hjl) (congrArg Prod.snd h))
    (by intro h; exact (ne_of_lt hik) (congrArg Prod.fst h))
    (by intro h; exact (ne_of_gt hik) (congrArg Prod.fst h))
    (by intro h; exact (ne_of_gt hjl) (congrArg Prod.snd h))
    (by intro h; exact (ne_of_lt hik) (congrArg Prod.fst h))
    (hcross i k j l hik hjl)
  have hrevC : key (k, l) ≠ key (i, l) := by
    intro h
    exact (ne_of_gt hik) (congrArg Prod.fst (hkey h))
  have hrevR : key (k, l) ≠ key (k, j) := by
    intro h
    exact (ne_of_gt hjl) (congrArg Prod.snd (hkey h))
  rw [key_indicator_reverse (key (k, l)) (key (i, l)) hrevC,
    key_indicator_reverse (key (k, l)) (key (k, j)) hrevR] at hodd
  change Odd (R i j l + C j i k + (1 - C l i k) + (1 - R k j l)) at hodd
  have heq : R i j l + C j i k + (1 - C l i k) + (1 - R k j l) =
      2 + R i j l - R k j l + C j i k - C l i k := by ring
  rw [heq] at hodd
  exact hodd

#print axioms nine_grid_key_crossings_impossible
#assert_trust kernel nine_grid_key_crossings_impossible

end NLA.NR04
