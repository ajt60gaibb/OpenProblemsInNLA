/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

Actual candidate counting for Matthew J. Colbrook's NR-04 proof, University
of Cambridge. The exceptional distinct 3-by-3 crossing case is retained as
an explicit disjunct, not assumed impossible or hidden in a premise.
-/
import NLA.NR04.RankFourHeight
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace NLA.NR04

def heightZeroFamily {N k : ℕ} (h : (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (v : Fin k → Fin N → ℝ) : ZeroHeightIndices (fun i => h (v i)) → (Fin N → ℝ) :=
  fun l => v l.val

def heightCrossingFamily {N k : ℕ} (h : (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (v : Fin k → Fin N → ℝ) :
    PositiveHeightIndices (fun i => h (v i)) ×
      NegativeHeightIndices (fun i => h (v i)) → (Fin N → ℝ) :=
  fun ij => sliceCrossPoint (h (v ij.1.val)) (-h (v ij.2.val)) (v ij.1.val) (v ij.2.val)

lemma heightSliceCandidates_eq_ranges {N k : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ) :
    heightSliceCandidates h v =
      Set.range (heightZeroFamily h v) ∪ Set.range (heightCrossingFamily h v) := rfl

/-- Index counts bound the actual range; no distinctness hypothesis is needed. -/
lemma height_range_ncard_le {I A : Type*} [Fintype I] (f : I → A) :
    (Set.range f).ncard ≤ Fintype.card I := by
  have hh := Set.ncard_image_le (f := f) (s := Set.univ) (Set.toFinite Set.univ)
  simpa only [Set.image_univ, Set.ncard_univ, Nat.card_eq_fintype_card] using hh

/-- A repeated candidate strictly reduces the true finite range cardinality. -/
lemma height_range_ncard_lt_of_not_injective {I A : Type*} [Fintype I]
    (f : I → A) (hf : ¬ Function.Injective f) :
    (Set.range f).ncard < Fintype.card I := by
  apply lt_of_le_of_ne (height_range_ncard_le f)
  intro heq
  apply hf
  have himage : (f '' (Set.univ : Set I)).ncard = (Set.univ : Set I).ncard := by
    simpa only [Set.image_univ, Set.ncard_univ, Nat.card_eq_fintype_card] using heq
  simpa only [Set.injOn_univ] using
    Set.injOn_of_ncard_image_eq himage (Set.toFinite Set.univ)

/-- Every candidate is an actual value of one of two finite families. -/
lemma height_candidates_finite {N k : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ) :
    (heightSliceCandidates h v).Finite := by
  rw [heightSliceCandidates_eq_ranges]
  exact (Set.finite_range _).union (Set.finite_range _)

/-- The usual z+p*q count is an upper bound, not an assertion that the
supplied candidates are all distinct or extreme. -/
lemma height_candidates_ncard_le {N k : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ) :
    (heightSliceCandidates h v).ncard ≤
      Fintype.card (ZeroHeightIndices (fun i => h (v i))) +
      Fintype.card (PositiveHeightIndices (fun i => h (v i))) *
        Fintype.card (NegativeHeightIndices (fun i => h (v i))) := by
  rw [heightSliceCandidates_eq_ranges]
  refine (Set.ncard_union_le _ _).trans
    (Nat.add_le_add (height_range_ncard_le (heightZeroFamily h v)) ?_)
  simpa only [Fintype.card_prod] using height_range_ncard_le (heightCrossingFamily h v)

/-- The sharper bound uses the true candidate set and therefore automatically
retains all coincidences among crossing and zero-height candidates. -/
lemma height_slice_extreme_bound_actual_candidates {N k : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ) :
    ((convexHull ℝ (Set.range v) ∩ {x | h x = 0}).extremePoints ℝ).Finite ∧
      ((convexHull ℝ (Set.range v) ∩ {x | h x = 0}).extremePoints ℝ).ncard ≤
        (heightSliceCandidates h v).ncard := by
  rw [finite_height_slice_eq]
  have hsub : (convexHull ℝ (heightSliceCandidates h v)).extremePoints ℝ ⊆
      heightSliceCandidates h v := extremePoints_convexHull_subset
  have hfin := height_candidates_finite h v
  exact ⟨hfin.subset hsub, Set.ncard_le_ncard hsub hfin⟩

lemma height_slice_bound_of_candidate_ncard_le_eight {N k : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ)
    (hc : (heightSliceCandidates h v).ncard ≤ 8) :
    ((convexHull ℝ (Set.range v) ∩ {x | h x = 0}).extremePoints ℝ).Finite ∧
      ((convexHull ℝ (Set.range v) ∩ {x | h x = 0}).extremePoints ℝ).ncard ≤ 8 := by
  obtain ⟨hfin, hle⟩ := height_slice_extreme_bound_actual_candidates h v
  exact ⟨hfin, hle.trans hc⟩

/-- Only the 3+3 partition can exceed eight candidate indices. The bounded
cases are just p,q; z remains an arbitrary natural constrained by the sum. -/
lemma six_height_partition_nonexceptional (p q z : ℕ)
    (hsum : p + q + z ≤ 6) (hex : ¬ (p = 3 ∧ q = 3 ∧ z = 0)) :
    z + p * q ≤ 8 := by
  have hp : p ≤ 6 := by omega
  have hq : q ≤ 6 := by omega
  interval_cases p <;> interval_cases q <;> omega

/-- All nonexceptional partitions of at most six original columns satisfy
the true extreme-point bound, including one-sided or all-zero heights. -/
lemma height_slice_nonexceptional_bound {N k : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ) (hk : k ≤ 6)
    (hex : ¬ (Fintype.card (PositiveHeightIndices (fun i => h (v i))) = 3 ∧
      Fintype.card (NegativeHeightIndices (fun i => h (v i))) = 3 ∧
      Fintype.card (ZeroHeightIndices (fun i => h (v i))) = 0)) :
    ((convexHull ℝ (Set.range v) ∩ {x | h x = 0}).extremePoints ℝ).Finite ∧
      ((convexHull ℝ (Set.range v) ∩ {x | h x = 0}).extremePoints ℝ).ncard ≤ 8 := by
  apply height_slice_bound_of_candidate_ncard_le_eight
  apply (height_candidates_ncard_le h v).trans
  apply six_height_partition_nonexceptional _ _ _ _ hex
  simpa only [height_partition_card] using hk

/-- Even the 3-by-3 index partition is already settled if two actual
crossings coincide. No generic-position assumption discards this case. -/
lemma height_slice_duplicate_exception_bound {N k : ℕ}
    (h : (Fin N → ℝ) →ₗ[ℝ] ℝ) (v : Fin k → Fin N → ℝ)
    (hp : Fintype.card (PositiveHeightIndices (fun i => h (v i))) = 3)
    (hq : Fintype.card (NegativeHeightIndices (fun i => h (v i))) = 3)
    (hz : Fintype.card (ZeroHeightIndices (fun i => h (v i))) = 0)
    (hdup : ¬ Function.Injective (heightCrossingFamily h v)) :
    ((convexHull ℝ (Set.range v) ∩ {x | h x = 0}).extremePoints ℝ).Finite ∧
      ((convexHull ℝ (Set.range v) ∩ {x | h x = 0}).extremePoints ℝ).ncard ≤ 8 := by
  apply height_slice_bound_of_candidate_ncard_le_eight
  letI : IsEmpty (ZeroHeightIndices (fun i => h (v i))) :=
    Fintype.card_eq_zero_iff.mp hz
  rw [heightSliceCandidates_eq_ranges, Set.range_eq_empty, Set.empty_union]
  have hh := height_range_ncard_lt_of_not_injective (heightCrossingFamily h v) hdup
  rw [Fintype.card_prod, hp, hq] at hh
  omega

/-- Honest reduction of the rank-four C08 branch: either the true bound is
proved, or the actual height has the still-unresolved distinct 3-by-3 form.
The difficult exceptional geometry is not asserted by this theorem. -/
lemma rank_four_section_bound_or_distinct_exception {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hk : k ≤ 6) (hU : ColumnStochastic U) (hX : ColumnStochastic X)
    (hrU : U.rank = 4) (hrX : X.rank = 3)
    (hcontain : columnSet X ⊆ columnHull U) :
    (((columnSection U X).extremePoints ℝ).Finite ∧
      ((columnSection U X).extremePoints ℝ).ncard ≤ 8) ∨
    ∃ h : (Fin N → ℝ) →ₗ[ℝ] ℝ, h ≠ 0 ∧
      columnSection U X = convexHull ℝ (heightSliceCandidates h U.col) ∧
      Fintype.card (PositiveHeightIndices (fun i => h (U.col i))) = 3 ∧
      Fintype.card (NegativeHeightIndices (fun i => h (U.col i))) = 3 ∧
      Fintype.card (ZeroHeightIndices (fun i => h (U.col i))) = 0 ∧
      Function.Injective (heightCrossingFamily h U.col) := by
  obtain ⟨h, hne, _, hsection⟩ :=
    rank_four_column_section_height U X hU hX hrU hrX hcontain
  by_cases hex : Fintype.card (PositiveHeightIndices (fun i => h (U.col i))) = 3 ∧
      Fintype.card (NegativeHeightIndices (fun i => h (U.col i))) = 3 ∧
      Fintype.card (ZeroHeightIndices (fun i => h (U.col i))) = 0
  · by_cases hinj : Function.Injective (heightCrossingFamily h U.col)
    · right
      exact ⟨h, hne, hsection.trans (finite_height_slice_eq h U.col),
        hex.1, hex.2.1, hex.2.2, hinj⟩
    · left
      rw [hsection]
      exact height_slice_duplicate_exception_bound h U.col hex.1 hex.2.1 hex.2.2 hinj
  · left
    rw [hsection]
    exact height_slice_nonexceptional_bound h U.col hk hex

#print axioms height_candidates_ncard_le
#print axioms height_slice_extreme_bound_actual_candidates
#print axioms six_height_partition_nonexceptional
#print axioms height_slice_duplicate_exception_bound
#print axioms rank_four_section_bound_or_distinct_exception

end NLA.NR04
