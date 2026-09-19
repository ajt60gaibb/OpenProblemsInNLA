/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Actual height-crossing enumeration for Matthew J. Colbrook's NR-04 argument,
University of Cambridge. The finite equivalences preserve the crossing family
and its full hull; actual positive-height diagonal certificates are consumed.
-/
import NLA.NR04.ColumnPlaneGridObstruction
import NLA.NR04.HeightCandidateCount
import NLA.NR04.CrossingRectangles
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Classical

namespace NLA.NR04

theorem height_crossings_not_all_extreme_in_column_plane {N k : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : ColumnStochastic X) (hrX : X.rank = 3)
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ)
    (hp : Fintype.card (PositiveHeightIndices (fun i => h (v i))) = 3)
    (hq : Fintype.card (NegativeHeightIndices (fun i => h (v i))) = 3)
    (hinj : Function.Injective (heightCrossingFamily h v))
    (hmem : Set.range (heightCrossingFamily h v) ⊆
      (columnAffineSpan X : Set (Fin N → ℝ))) :
    ¬ (∀ a, heightCrossingFamily h v a ∈
      (convexHull ℝ (Set.range (heightCrossingFamily h v))).extremePoints ℝ) := by
  intro hext
  let ep : Fin 3 ≃ PositiveHeightIndices (fun i => h (v i)) :=
    (Fintype.equivFinOfCardEq hp).symm
  let en : Fin 3 ≃ NegativeHeightIndices (fun i => h (v i)) :=
    (Fintype.equivFinOfCardEq hq).symm
  let e : (Fin 3 × Fin 3) ≃
      (PositiveHeightIndices (fun i => h (v i)) ×
        NegativeHeightIndices (fun i => h (v i))) := ep.prodCongr en
  let w : Fin 3 × Fin 3 → Fin N → ℝ := fun a => heightCrossingFamily h v (e a)
  have hw : Function.Injective w := hinj.comp e.injective
  have hrange : Set.range w = Set.range (heightCrossingFamily h v) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e a, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨e.symm a, ?_⟩
      dsimp [w]
      rw [e.apply_symm_apply]
  have hmemw : ∀ a, w a ∈ columnAffineSpan X := by
    intro a
    exact hmem (Set.mem_range_self (e a))
  have hcross : ∀ i k j l : Fin 3, i < k → j < l →
      (openSegment ℝ (w (i, j)) (w (k, l)) ∩
        openSegment ℝ (w (i, l)) (w (k, j))).Nonempty := by
    intro i k j l _ _
    exact slice_cross_diagonals_intersect
      (h (v (ep i).val)) (h (v (ep k).val))
      (-h (v (en j).val)) (-h (v (en l).val))
      (v (ep i).val) (v (ep k).val) (v (en j).val) (v (en l).val)
      (ep i).property (ep k).property
      (neg_pos.mpr (en j).property) (neg_pos.mpr (en l).property)
  apply nine_grid_in_column_plane_not_all_extreme X hX hrX w hw hmemw hcross
  intro a
  rw [hrange]
  exact hext (e a)

#print axioms height_crossings_not_all_extreme_in_column_plane
#assert_trust kernel height_crossings_not_all_extreme_in_column_plane

end NLA.NR04
