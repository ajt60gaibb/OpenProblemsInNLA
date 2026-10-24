/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
import NLA.TR06.ProjectionCompact

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal Topology
open MeasureTheory Set Function Metric Module Filter

namespace NLA.TR06.Area.Proposed

/-- The frame bound controls the inverse coordinate projection on every tangent
plane, independently of the conditioning of its initial parametrization. -/
theorem uniform_tangent_coordinate_bound (m N : ℕ) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ A : Euclid m →L[ℝ] Euclid N, Injective A →
      ∃ σ : Fin m ↪ Fin N, ∀ x, ‖A x‖ ≤ (K : ℝ) * ‖coordProjectionL σ (A x)‖ := by
  classical
  obtain ⟨K, hK, hbound⟩ := uniform_isometric_coordinate_bound m N
  refine ⟨K, hK, ?_⟩
  intro A hA
  have hdim : Module.finrank ℝ A.toLinearMap.range = m := by
    simpa only [finrank_euclideanSpace_fin] using LinearMap.finrank_range_of_inj hA
  let b : OrthonormalBasis (Fin m) ℝ A.toLinearMap.range :=
    (stdOrthonormalBasis ℝ A.toLinearMap.range).reindex (finCongr hdim)
  let L : Euclid m →ₗᵢ[ℝ] Euclid N :=
    A.toLinearMap.range.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  obtain ⟨σ, hσ⟩ := hbound L.toContinuousLinearMap L.norm_map
  refine ⟨σ, ?_⟩
  intro x
  let v : A.toLinearMap.range := A.rangeRestrict x
  have hLv : L (b.repr v) = A x := by
    change ((b.repr.symm (b.repr v) : A.toLinearMap.range) : Euclid N) = A x
    rw [b.repr.symm_apply_apply]
    rfl
  have H := hσ (b.repr v)
  change ‖b.repr v‖ ≤ (K : ℝ) * ‖coordProjectionL σ (L (b.repr v))‖ at H
  rw [hLv, b.repr.norm_map] at H
  exact H

/-- Package a tangent coordinate projection as a genuine equivalence; its
inverse followed by the original immersion derivative has the uniform norm bound. -/
theorem tangent_coordinate_equiv {m N : ℕ} {K : ℝ≥0}
    (A : Euclid m →L[ℝ] Euclid N) (hA : Injective A)
    (σ : Fin m ↪ Fin N)
    (hbound : ∀ x, ‖A x‖ ≤ (K : ℝ) * ‖coordProjectionL σ (A x)‖) :
    ∃ e : Euclid m ≃L[ℝ] Euclid m,
      (e : Euclid m →L[ℝ] Euclid m) = (coordProjectionL σ).comp A ∧
      ‖A.comp (e.symm : Euclid m →L[ℝ] Euclid m)‖ ≤ K := by
  have hinj : Injective ((coordProjectionL σ).comp A) := by
    intro x y hxy
    have H := hbound (x - y)
    have hz : coordProjectionL σ (A (x - y)) = 0 := by
      simpa only [map_sub, sub_eq_zero, ContinuousLinearMap.comp_apply] using hxy
    rw [hz, norm_zero, mul_zero] at H
    apply hA
    exact sub_eq_zero.mp (by simpa only [map_sub] using norm_eq_zero.mp (le_antisymm H (norm_nonneg _)))
  let e : Euclid m ≃L[ℝ] Euclid m :=
    (LinearEquiv.ofBijective ((coordProjectionL σ).comp A).toLinearMap
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have he : (e : Euclid m →L[ℝ] Euclid m) = (coordProjectionL σ).comp A := rfl
  refine ⟨e, he, ContinuousLinearMap.opNorm_le_bound _ K.2 ?_⟩
  intro x
  have H := hbound (e.symm x)
  have hx : coordProjectionL σ (A (e.symm x)) = x := by
    change ((coordProjectionL σ).comp A) (e.symm x) = x
    rw [← he]
    exact e.apply_symm_apply x
  rw [hx] at H
  exact H

#print axioms uniform_tangent_coordinate_bound
#print axioms tangent_coordinate_equiv
#assert_trust kernel uniform_tangent_coordinate_bound
#assert_trust kernel tangent_coordinate_equiv

end NLA.TR06.Area.Proposed
