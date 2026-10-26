/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
import NLA.TR06.ProjectionAtlasDefinitions
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal
open MeasureTheory Set Function Metric Module Matrix Submodule

namespace NLA.TR06.Area.Proposed

/-- An injective rectangular matrix has an invertible coordinate-row restriction.
The proof extracts a basis from its spanning row family, without Cauchy–Binet. -/
theorem matrix_exists_injective_row_restriction {m N : ℕ}
    (A : Matrix (Fin N) (Fin m) ℝ) (hA : Injective A.mulVec) :
    ∃ σ : Fin m ↪ Fin N, Injective (A.submatrix σ id).mulVec := by
  classical
  have hspan : Submodule.span ℝ (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← A.rank_eq_finrank_span_row]
    exact LinearMap.finrank_range_of_inj hA
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℝ A.row
  let : Fintype κ := Fintype.ofInjective a ha
  let b : Basis κ ℝ (Fin m → ℝ) := Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card κ = m := by
    simpa using (Module.finrank_eq_card_basis b).symm
  let e : κ ≃ Fin m := Fintype.equivFinOfCardEq hcard
  let σ : Fin m ↪ Fin N := ⟨a ∘ e.symm, ha.comp e.symm.injective⟩
  refine ⟨σ, Matrix.mulVec_injective_iff_isUnit.mpr ?_⟩
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  exact hli.comp e.symm e.symm.injective

/-- Coordinate restriction as a continuous linear map. -/
def coordProjectionL {m N : ℕ} (σ : Fin m ↪ Fin N) : Euclid N →L[ℝ] Euclid m :=
  (show Euclid N →ₗ[ℝ] Euclid m from
    { toFun := coordProjection σ
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }).toContinuousLinearMap

@[simp] theorem coordProjectionL_apply {m N : ℕ} (σ : Fin m ↪ Fin N) (x : Euclid N) :
    coordProjectionL σ x = coordProjection σ x := rfl

/-- Every injective Euclidean linear map admits an injective coordinate projection. -/
theorem exists_injective_coordinate_projection {m N : ℕ}
    (A : Euclid m →L[ℝ] Euclid N) (hA : Injective A) :
    ∃ σ : Fin m ↪ Fin N, Injective ((coordProjectionL σ).comp A) := by
  classical
  let e := EuclideanSpace.equiv (Fin m) ℝ
  let g := EuclideanSpace.equiv (Fin N) ℝ
  let B := g.toLinearMap.comp (A.toLinearMap.comp e.symm.toLinearMap)
  let M := LinearMap.toMatrix' B
  have hM : Injective M.mulVec := by
    have hB : Injective B := g.injective.comp (hA.comp e.symm.injective)
    intro x y hxy
    apply hB
    simpa only [M, LinearMap.toMatrix'_mulVec] using hxy
  obtain ⟨σ, hσ⟩ := matrix_exists_injective_row_restriction M hM
  refine ⟨σ, ?_⟩
  intro x y hxy
  apply e.injective
  apply hσ
  ext i
  have hi := congrArg (fun z : Euclid m => z i) hxy
  change (M *ᵥ e x) (σ i) = (M *ᵥ e y) (σ i)
  simp only [M, LinearMap.toMatrix'_mulVec, B, LinearMap.comp_apply]
  change (A (e.symm (e x))) (σ i) = (A (e.symm (e y))) (σ i)
  rw [e.symm_apply_apply, e.symm_apply_apply]
  exact hi

#print axioms matrix_exists_injective_row_restriction
#print axioms exists_injective_coordinate_projection
#assert_trust kernel matrix_exists_injective_row_restriction
#assert_trust kernel exists_injective_coordinate_projection

end NLA.TR06.Area.Proposed
