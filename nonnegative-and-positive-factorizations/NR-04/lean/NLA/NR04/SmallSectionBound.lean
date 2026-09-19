/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

The exact frozen C08 statement for Matthew J. Colbrook's NR-04 argument,
University of Cambridge. The finite-crossing implementation closes the genuine
exception while retaining duplicate/nonextreme generators and all rank cases.
This source does not import Challenge or assert C09/the full NR-04 target.
-/
import NLA.NR04.ExceptionalHeightBound
import NLA.NR04.SmallSectionRankThree

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Classical

namespace NLA.NR04

theorem rank_four_section_bound {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hk : k ≤ 6) (hU : ColumnStochastic U) (hX : ColumnStochastic X)
    (hrU : U.rank = 4) (hrX : X.rank = 3)
    (hcontain : columnSet X ⊆ columnHull U) :
    ((columnSection U X).extremePoints ℝ).Finite ∧
      ((columnSection U X).extremePoints ℝ).ncard ≤ 8 := by
  rcases rank_four_section_bound_or_distinct_exception U X hk hU hX hrU hrX hcontain with
    hgood | ⟨h, _, hsection, hp, hq, hz, hinj⟩
  · exact hgood
  · have hmem : Set.range (heightCrossingFamily h U.col) ⊆
        (columnAffineSpan X : Set (Fin N → ℝ)) := by
      rintro x ⟨a, rfl⟩
      have hc : heightCrossingFamily h U.col a ∈ heightSliceCandidates h U.col := by
        rw [heightSliceCandidates_eq_ranges]
        exact Or.inr (Set.mem_range_self a)
      have hs : heightCrossingFamily h U.col a ∈ columnSection U X := by
        rw [hsection]
        exact subset_convexHull ℝ _ hc
      exact hs.2
    rw [hsection]
    exact height_distinct_exception_bound_in_column_plane X hX hrX h U.col
      hp hq hz hinj hmem

/-- The original C08, with exactly its frozen hypotheses and actual section.
The rank-three case and every rank-four height case are proved internally. -/
theorem small_section_bound {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hk : k ≤ 6) (hU : ColumnStochastic U) (hX : ColumnStochastic X)
    (hrU : U.rank ≤ 4) (hrX : X.rank = 3)
    (hcontain : columnSet X ⊆ columnHull U) :
    ((columnSection U X).extremePoints ℝ).Finite ∧
      ((columnSection U X).extremePoints ℝ).ncard ≤ 8 := by
  by_cases hr4 : U.rank = 4
  · exact rank_four_section_bound U X hk hU hX hr4 hrX hcontain
  · have hr3 : U.rank ≤ 3 := by omega
    obtain ⟨hfin, hle⟩ :=
      small_section_bound_of_rank_le_three U X hU hX hr3 hrX hcontain
    exact ⟨hfin, hle.trans (by omega)⟩

#print axioms rank_four_section_bound
#print axioms small_section_bound
#assert_trust kernel rank_four_section_bound
#assert_trust kernel small_section_bound

end NLA.NR04
