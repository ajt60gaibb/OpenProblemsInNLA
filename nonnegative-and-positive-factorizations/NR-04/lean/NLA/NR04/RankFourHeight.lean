/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

Rank-to-height prerequisites for Matthew J. Colbrook's NR-04 proof,
University of Cambridge. The ambient functional is constructed using actual
linear algebra. No assumed polygon, cyclic ordering, or vertex bound is used.
-/
import NLA.NR04.SmallSectionRankThree
import NLA.NR04.FiniteHeightSlice
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.NR04

/-- Actual ambient linear height for a nested pair of subspaces whose finite
dimensions differ by one. It is obtained from a separating vector and linear
extension; the restricted kernel identity follows from dimension comparison. -/
lemma exists_linear_height_of_finrank_succ {N d : ℕ}
    (W V : Submodule ℝ (Fin N → ℝ)) (hWV : W ≤ V)
    (hW : Module.finrank ℝ W = d) (hV : Module.finrank ℝ V = d + 1) :
    ∃ h : (Fin N → ℝ) →ₗ[ℝ] ℝ, h ≠ 0 ∧ W = V ⊓ h.ker := by
  classical
  have hlt : W < V := Submodule.lt_of_le_of_finrank_lt_finrank hWV (by
    rw [hW, hV]
    exact Nat.lt_succ_self d)
  obtain ⟨v, hvV, hvW⟩ := SetLike.exists_of_lt hlt
  obtain ⟨h, hvnonzero, hWker⟩ := Submodule.exists_le_ker_of_notMem hvW
  have hproper : V ⊓ h.ker < V := by
    apply lt_of_le_not_ge inf_le_left
    intro hle
    have hv : v ∈ V ⊓ h.ker := hle hvV
    exact hvnonzero hv.2
  have hdim : Module.finrank ℝ ↥(V ⊓ h.ker) ≤ d := by
    have hh := Submodule.finrank_lt_finrank_of_lt hproper
    rw [hV] at hh
    exact Nat.le_of_lt_succ hh
  have heq : W = V ⊓ h.ker :=
    Submodule.eq_of_le_of_finrank_le (le_inf hWV hWker) (by simpa only [hW] using hdim)
  refine ⟨h, ?_, heq⟩
  intro hz
  apply hvnonzero
  simp only [hz, LinearMap.zero_apply]

/-- Every actual convex combination of normalized columns has coordinate
sum one, with no square-matrix restriction on the outer family. -/
lemma sum_eq_one_of_mem_columnHull {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : ColumnStochastic U)
    (y : Fin N → ℝ) (hy : y ∈ columnHull U) : ∑ i, y i = 1 := by
  change y ∈ convexHull ℝ (Set.range U.col) at hy
  obtain ⟨c, _, hc1, hcy⟩ := mem_finite_range_convexHull_weights U.col y hy
  rw [← hcy]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simpa only [hU.2, mul_one] using hc1

/-- Rank four versus rank three constructs a genuine linear height for the
actual normalized column section. The kernel/affine-span equivalence is only
restricted to the outer hull, where normalization supplies coordinate sum one. -/
lemma rank_four_column_section_height {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hU : ColumnStochastic U) (hX : ColumnStochastic X)
    (hrU : U.rank = 4) (hrX : X.rank = 3)
    (hcontain : columnSet X ⊆ columnHull U) :
    ∃ h : (Fin N → ℝ) →ₗ[ℝ] ℝ, h ≠ 0 ∧
      (∀ y ∈ columnHull U, (y ∈ columnAffineSpan X ↔ h y = 0)) ∧
      columnSection U X = columnHull U ∩ {y | h y = 0} := by
  let V := LinearMap.range U.mulVecLin
  let W := LinearMap.range X.mulVecLin
  have hspan : Submodule.span ℝ (Set.range X.col) ≤
      Submodule.span ℝ (Set.range U.col) := by
    apply Submodule.span_le.mpr
    intro y hy
    apply affineSpan_subset_span (k := ℝ)
    exact convexHull_subset_affineSpan (columnSet U) (hcontain hy)
  have hWV : W ≤ V := by
    simpa only [W, V, Matrix.range_mulVecLin] using hspan
  have hW : Module.finrank ℝ W = 3 := hrX
  have hV : Module.finrank ℝ V = 3 + 1 := hrU
  obtain ⟨h, hne, hker⟩ := exists_linear_height_of_finrank_succ W V hWV hW hV
  have hiff : ∀ y ∈ columnHull U, (y ∈ columnAffineSpan X ↔ h y = 0) := by
    intro y hyHull
    constructor
    · intro hyX
      have hyspan : y ∈ Submodule.span ℝ (Set.range X.col) :=
        affineSpan_subset_span (k := ℝ) hyX
      have hyW : y ∈ W := by
        simpa only [W, Matrix.range_mulVecLin] using hyspan
      rw [hker] at hyW
      exact hyW.2
    · intro hyzero
      have hyspan : y ∈ Submodule.span ℝ (Set.range U.col) :=
        affineSpan_subset_span (k := ℝ)
          (convexHull_subset_affineSpan (columnSet U) hyHull)
      have hyV : y ∈ V := by
        simpa only [V, Matrix.range_mulVecLin] using hyspan
      have hyW : y ∈ W := by
        rw [hker]
        exact ⟨hyV, hyzero⟩
      apply mem_columnAffineSpan_of_mem_span_sum_one X hX y _
        (sum_eq_one_of_mem_columnHull U hU y hyHull)
      simpa only [W, Matrix.range_mulVecLin] using hyW
  refine ⟨h, hne, hiff, ?_⟩
  ext y
  change (y ∈ columnHull U ∧ y ∈ columnAffineSpan X) ↔
    (y ∈ columnHull U ∧ h y = 0)
  exact and_congr_right (hiff y)

/-- The rank-derived height and the proved finite-slice identity now describe
the actual NR-04 column section by its actual zero-height/crossing candidates.
This gives no unproved bound on their number or on the extreme points. -/
lemma rank_four_column_section_candidates {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hU : ColumnStochastic U) (hX : ColumnStochastic X)
    (hrU : U.rank = 4) (hrX : X.rank = 3)
    (hcontain : columnSet X ⊆ columnHull U) :
    ∃ h : (Fin N → ℝ) →ₗ[ℝ] ℝ, h ≠ 0 ∧
      columnSection U X = convexHull ℝ (heightSliceCandidates h U.col) := by
  obtain ⟨h, hne, _, hsection⟩ :=
    rank_four_column_section_height U X hU hX hrU hrX hcontain
  refine ⟨h, hne, hsection.trans ?_⟩
  exact finite_height_slice_eq h U.col

#print axioms exists_linear_height_of_finrank_succ
#print axioms sum_eq_one_of_mem_columnHull
#print axioms rank_four_column_section_height
#print axioms rank_four_column_section_candidates

end NLA.NR04
