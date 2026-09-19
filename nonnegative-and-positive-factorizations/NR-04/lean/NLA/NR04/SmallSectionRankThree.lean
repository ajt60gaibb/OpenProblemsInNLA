/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

The lower-dimensional branch of frozen NR-04 C08, from Matthew J. Colbrook's
proof, University of Cambridge. This module does not assert C08 for rank-four
outer generators. That genuine three-dimensional polytope bound remains.
-/
import NLA.NR04.SectionLinearAlgebra
import Mathlib.Analysis.Convex.Combination

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix

namespace NLA.NR04

/-- In normalized columns, linear-span membership and coordinate sum one
already give membership in the actual affine span. Negative coefficients
are allowed, as is necessary for an affine span statement. -/
lemma mem_columnAffineSpan_of_mem_span_sum_one {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : ColumnStochastic X)
    (v : Fin N → ℝ) (hv : v ∈ Submodule.span ℝ (Set.range X.col))
    (hvsum : ∑ i, v i = 1) : v ∈ columnAffineSpan X := by
  have hvRange : v ∈ LinearMap.range X.mulVecLin := by
    rwa [Matrix.range_mulVecLin]
  obtain ⟨c, hc⟩ := hvRange
  change X *ᵥ c = v at hc
  have hcsum : ∑ j, c j = 1 := by
    calc
      (∑ j, c j) = ∑ j, (∑ i, X i j) * c j := by simp [hX.2]
      _ = ∑ j, ∑ i, X i j * c j := by simp only [Finset.sum_mul]
      _ = ∑ i, ∑ j, X i j * c j := Finset.sum_comm
      _ = ∑ i, v i := by rw [← hc]; rfl
      _ = 1 := hvsum
  have hcomb : (∑ j, c j • X.col j) = v := by
    ext i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
      Matrix.mulVec, dotProduct, mul_comm] using congrFun hc i
  have hmem := affineCombination_mem_affineSpan
    (s := Finset.univ) hcsum X.col
  rw [Finset.affineCombination_eq_linear_combination Finset.univ X.col c hcsum,
    hcomb] at hmem
  exact hmem

/-- If both containing and contained normalized column families have linear
rank three, the full containing convex hull lies in the contained affine
plane. Repeated and nonextreme outer columns cause no exception. -/
lemma columnHull_subset_columnAffineSpan_of_rank_le_three {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hU : ColumnStochastic U) (hX : ColumnStochastic X)
    (hrU : U.rank ≤ 3) (hrX : X.rank = 3)
    (hcontain : columnSet X ⊆ columnHull U) :
    columnHull U ⊆ (columnAffineSpan X : Set (Fin N → ℝ)) := by
  have hspan : Submodule.span ℝ (Set.range X.col) ≤
      Submodule.span ℝ (Set.range U.col) := by
    apply Submodule.span_le.mpr
    intro x hx
    apply affineSpan_subset_span (k := ℝ)
    exact convexHull_subset_affineSpan (columnSet U) (hcontain hx)
  have hrange : LinearMap.range X.mulVecLin = LinearMap.range U.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_le
    · simpa only [Matrix.range_mulVecLin] using hspan
    · change U.rank ≤ X.rank
      simpa only [hrX] using hrU
  have hgen : columnSet U ⊆ (columnAffineSpan X : Set (Fin N → ℝ)) := by
    rintro _ ⟨j, rfl⟩
    apply mem_columnAffineSpan_of_mem_span_sum_one X hX (fun i => U i j) _ (hU.2 j)
    have hUmem : (fun i => U i j) ∈ LinearMap.range U.mulVecLin := by
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨j, rfl⟩
    rw [← hrange, Matrix.range_mulVecLin] at hUmem
    exact hUmem
  exact convexHull_min hgen (columnAffineSpan X).convex

/-- Genuine C08 subcase: for outer rank at most three the exact section has
at most k extreme points. The full C08 rank-four case is not claimed here. -/
lemma small_section_bound_of_rank_le_three {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hU : ColumnStochastic U) (hX : ColumnStochastic X)
    (hrU : U.rank ≤ 3) (hrX : X.rank = 3)
    (hcontain : columnSet X ⊆ columnHull U) :
    ((columnSection U X).extremePoints ℝ).Finite ∧
      ((columnSection U X).extremePoints ℝ).ncard ≤ k := by
  classical
  have heq : columnSection U X = columnHull U :=
    Set.inter_eq_left.mpr
      (columnHull_subset_columnAffineSpan_of_rank_le_three U X hU hX hrU hrX hcontain)
  have hsub : (columnHull U).extremePoints ℝ ⊆ columnSet U :=
    extremePoints_convexHull_subset
  have hfin : (columnSet U).Finite := Set.finite_range (fun j => fun i => U i j)
  have hcard : (columnSet U).ncard ≤ k := by
    let f : Fin k → (Fin N → ℝ) := fun j => fun i => U i j
    have h := Set.ncard_image_le (f := f) (s := Set.univ) (Set.toFinite Set.univ)
    simpa [f, columnSet, Set.image_univ] using h
  rw [heq]
  exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans hcard⟩

#print axioms mem_columnAffineSpan_of_mem_span_sum_one
#print axioms columnHull_subset_columnAffineSpan_of_rank_le_three
#print axioms small_section_bound_of_rank_le_three

end NLA.NR04
