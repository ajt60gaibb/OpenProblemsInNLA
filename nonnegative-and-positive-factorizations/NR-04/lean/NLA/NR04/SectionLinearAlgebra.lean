/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

These are linear-algebra prerequisites for the source's polygon-contact
argument, not a proof of C08 or C09. Mathematical source: Matthew J. Colbrook,
University of Cambridge, NR-04 manuscript, Lemmas 2--3. The finite-incidence
route described in GEOMETRY-ROUTE.md is an implementation alternative to
the manuscript's half-open normal-cone assignment, not a new canonical result.
-/
import NLA.NR04.Definitions
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix

namespace NLA.NR04

/-- Every three-by-three zero-diagonal positive-off-diagonal matrix is invertible. -/
lemma positive_offdiagonal_three_det (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hdiag : ∀ i, A i i = 0) (hoff : ∀ i j, i ≠ j → 0 < A i j) :
    0 < A.det := by
  have h₁ : 0 < A 0 1 * A 1 2 * A 2 0 :=
    mul_pos (mul_pos (hoff 0 1 (by decide)) (hoff 1 2 (by decide)))
      (hoff 2 0 (by decide))
  have h₂ : 0 < A 0 2 * A 1 0 * A 2 1 :=
    mul_pos (mul_pos (hoff 0 2 (by decide)) (hoff 1 0 (by decide)))
      (hoff 2 1 (by decide))
  simpa [Matrix.det_fin_three, hdiag] using add_pos h₁ h₂

/-- A nonzero principal three-minor makes its coordinates injective on a rank-three
column span. No stochasticity, nonnegativity or geometric assertion is assumed. -/
lemma rank_three_span_zero_of_three_coordinates {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hrX : X.rank = 3)
    (e : Fin 3 → Fin N) (hdet : (X.submatrix e e).det ≠ 0)
    (v : Fin N → ℝ) (hv : v ∈ Submodule.span ℝ (Set.range X.col))
    (hz : ∀ r, v (e r) = 0) : v = 0 := by
  let A : Matrix (Fin N) (Fin 3) ℝ := X.submatrix id e
  have hminor : (X.submatrix e e).rank = 3 := by
    simpa using Matrix.rank_of_det_ne_zero hdet
  have hrA : A.rank = 3 := by
    apply le_antisymm (Matrix.rank_le_width A)
    have h := Matrix.rank_submatrix_le A e id
    change (X.submatrix e e).rank ≤ A.rank at h
    simpa only [hminor] using h
  have hspan : Submodule.span ℝ (Set.range A.col) ≤
      Submodule.span ℝ (Set.range X.col) := by
    apply Submodule.span_mono
    rintro _ ⟨r, rfl⟩
    exact ⟨e r, rfl⟩
  have hrange : LinearMap.range A.mulVecLin = LinearMap.range X.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq
    · simpa only [Matrix.range_mulVecLin] using hspan
    · change A.rank = X.rank
      exact hrA.trans hrX.symm
  have hvRange : v ∈ LinearMap.range X.mulVecLin := by
    rwa [Matrix.range_mulVecLin]
  rw [← hrange] at hvRange
  obtain ⟨c, hc⟩ := hvRange
  change A *ᵥ c = v at hc
  have hproj : (X.submatrix e e) *ᵥ c = 0 := by
    ext r
    calc
      _ = (A *ᵥ c) (e r) := rfl
      _ = v (e r) := congrFun hc (e r)
      _ = 0 := hz r
  have hc0 : c = 0 :=
    (Matrix.mulVec_injective_of_det_ne_zero hdet) (by simpa using hproj)
  subst c
  simpa using hc.symm

/-- Every affine combination of normalized columns still has coordinate sum one. -/
lemma sum_eq_one_of_mem_columnAffineSpan {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : ColumnStochastic X)
    (v : Fin N → ℝ) (hv : v ∈ columnAffineSpan X) : ∑ i, v i = 1 := by
  change v ∈ affineSpan ℝ (columnSet X) at hv
  refine affineSpan_induction hv ?_ ?_
  · intro x hx
    obtain ⟨j, rfl⟩ := hx
    exact hX.2 j
  · intro c u v w hu hv hw
    change (∑ i : Fin N, (c * (u i - v i) + w i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hu, hv, hw]
    simp

/-- No affine-span point has three distinct zero coordinates. This is the actual
rank-three/strict-zero-pattern consequence behind the proposed incidence count. -/
lemma no_three_zero_coordinates {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : ColumnStochastic X)
    (hrX : X.rank = 3) (hdiag : ∀ i, X i i = 0)
    (hoff : ∀ i j, i ≠ j → 0 < X i j)
    (v : Fin N → ℝ) (hv : v ∈ columnAffineSpan X)
    (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (v i = 0 ∧ v j = 0 ∧ v k = 0) := by
  intro hz
  let e : Fin 3 → Fin N := ![i, j, k]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e]
  have hdet : (X.submatrix e e).det ≠ 0 := by
    apply ne_of_gt
    apply positive_offdiagonal_three_det
    · intro r
      exact hdiag (e r)
    · intro r s hrs
      exact hoff (e r) (e s) (fun h => hrs (he h))
  have hspan : v ∈ Submodule.span ℝ (Set.range X.col) := by
    exact affineSpan_subset_span (k := ℝ) hv
  have hz' : ∀ r, v (e r) = 0 := by
    intro r
    fin_cases r
    · simpa [e] using hz.1
    · simpa [e] using hz.2.1
    · simpa [e] using hz.2.2
  have hv0 := rank_three_span_zero_of_three_coordinates X hrX e hdet v hspan hz'
  have hvsum := sum_eq_one_of_mem_columnAffineSpan X hX v hv
  simp [hv0] at hvsum

/-- The finite zero-incidence degree bound needed by the counting route. -/
lemma zero_coordinate_card_le_two {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : ColumnStochastic X)
    (hrX : X.rank = 3) (hdiag : ∀ i, X i i = 0)
    (hoff : ∀ i j, i ≠ j → 0 < X i j)
    (v : Fin N → ℝ) (hv : v ∈ columnAffineSpan X) :
    (Finset.univ.filter fun i => v i = 0).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
  exact no_three_zero_coordinates X hX hrX hdiag hoff v hv i j k hij hik hjk
    ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2,
      (Finset.mem_filter.mp hk).2⟩

#print axioms positive_offdiagonal_three_det
#print axioms rank_three_span_zero_of_three_coordinates
#print axioms sum_eq_one_of_mem_columnAffineSpan
#print axioms no_three_zero_coordinates
#print axioms zero_coordinate_card_le_two

end NLA.NR04
