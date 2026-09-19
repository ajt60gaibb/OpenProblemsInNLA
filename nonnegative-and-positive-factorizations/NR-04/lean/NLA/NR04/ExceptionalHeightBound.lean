/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Actual finite candidate cardinality for Matthew J. Colbrook's NR-04 argument,
University of Cambridge. A proved nonextreme crossing gives a strict subset
of the actual finite candidate range; the desired bound is not assumed.
-/
import NLA.NR04.HeightCrossingObstruction

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Classical

namespace NLA.NR04

theorem height_distinct_exception_bound_in_column_plane {N k : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : ColumnStochastic X) (hrX : X.rank = 3)
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ)
    (hp : Fintype.card (PositiveHeightIndices (fun i => h (v i))) = 3)
    (hq : Fintype.card (NegativeHeightIndices (fun i => h (v i))) = 3)
    (hz : Fintype.card (ZeroHeightIndices (fun i => h (v i))) = 0)
    (hinj : Function.Injective (heightCrossingFamily h v))
    (hmem : Set.range (heightCrossingFamily h v) ⊆
      (columnAffineSpan X : Set (Fin N → ℝ))) :
    ((convexHull ℝ (heightSliceCandidates h v)).extremePoints ℝ).Finite ∧
      ((convexHull ℝ (heightSliceCandidates h v)).extremePoints ℝ).ncard ≤ 8 := by
  classical
  letI : IsEmpty (ZeroHeightIndices (fun i => h (v i))) := Fintype.card_eq_zero_iff.mp hz
  have hcand : heightSliceCandidates h v = Set.range (heightCrossingFamily h v) := by
    rw [heightSliceCandidates_eq_ranges, Set.range_eq_empty, Set.empty_union]
  rw [hcand]
  let F := heightCrossingFamily h v
  let E : Set (Fin N → ℝ) := (convexHull ℝ (Set.range F)).extremePoints ℝ
  change E.Finite ∧ E.ncard ≤ 8
  have hfin : (Set.range F).Finite := Set.finite_range F
  have hsub : E ⊆ Set.range F := extremePoints_convexHull_subset
  have hnot : ¬ (∀ a, F a ∈ E) :=
    height_crossings_not_all_extreme_in_column_plane X hX hrX h v hp hq hinj hmem
  obtain ⟨a, ha⟩ := not_forall.mp hnot
  have hstrict : E ⊂ Set.range F := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    apply ha
    rw [heq]
    exact Set.mem_range_self a
  have hlt : E.ncard < (Set.range F).ncard := Set.ncard_lt_ncard hstrict hfin
  have hbound : (Set.range F).ncard ≤ 9 := by
    have hh := height_range_ncard_le (heightCrossingFamily h v)
    rw [Fintype.card_prod, hp, hq] at hh
    exact hh
  exact ⟨hfin.subset hsub, by omega⟩

#print axioms height_distinct_exception_bound_in_column_plane
#assert_trust kernel height_distinct_exception_bound_in_column_plane

end NLA.NR04
