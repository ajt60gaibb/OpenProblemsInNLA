/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
import NLA.TR06.ProjectionLinear

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal Topology
open MeasureTheory Set Function Metric Module Filter

namespace NLA.TR06.Area.Proposed

def isometricOperators (m N : ℕ) : Set (Euclid m →L[ℝ] Euclid N) :=
  {A | ∀ x, ‖A x‖ = ‖x‖}

/-- The set of orthonormal frames, represented without a chosen basis, is compact.
This also includes the zero-dimensional domain. -/
theorem isCompact_isometricOperators (m N : ℕ) : IsCompact (isometricOperators m N) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · simp only [isometricOperators, ofPred_forall]
    exact isClosed_iInter fun x => isClosed_eq (by fun_prop) continuous_const
  · apply (Metric.isBounded_iff_subset_closedBall (0 : Euclid m →L[ℝ] Euclid N)).mpr
    refine ⟨1, ?_⟩
    intro A hA
    rw [mem_closedBall_zero_iff]
    apply ContinuousLinearMap.opNorm_le_bound A zero_le_one
    intro x
    simp only [hA x, one_mul, le_refl]

/-- An injective coordinate restriction has a uniform inverse norm bound throughout
an open operator neighborhood. This elementary perturbation bound avoids inversion. -/
theorem exists_coordinate_bound_neighborhood {m N : ℕ}
    (A : Euclid m →L[ℝ] Euclid N) (hA : Injective A) :
    ∃ (σ : Fin m ↪ Fin N) (K : ℝ≥0) (U : Set (Euclid m →L[ℝ] Euclid N)),
      0 < K ∧ IsOpen U ∧ A ∈ U ∧
      ∀ B ∈ U, ∀ x, ‖x‖ ≤ (K : ℝ) * ‖coordProjectionL σ (B x)‖ := by
  obtain ⟨σ, hσ⟩ := exists_injective_coordinate_projection A hA
  obtain ⟨K, hK, hanti⟩ := ((coordProjectionL σ).comp A).injective_iff_antilipschitz.mp hσ
  let δ : ℝ := (2 * (K : ℝ))⁻¹
  have hKr : (0 : ℝ) < K := hK
  have hδ : 0 < δ := by positivity
  have hKδ : (K : ℝ) * δ = 1 / 2 := by
    dsimp [δ]
    field_simp
  let U := {B : Euclid m →L[ℝ] Euclid N |
    ‖(coordProjectionL σ).comp B - (coordProjectionL σ).comp A‖ < δ}
  refine ⟨σ, 2 * K, U, by positivity, ?_, ?_, ?_⟩
  · exact isOpen_lt (by fun_prop) continuous_const
  · simp only [U, mem_ofPred_eq, sub_self, norm_zero]
    exact hδ
  · intro B hB x
    have hbase : ‖x‖ ≤ (K : ℝ) * ‖coordProjectionL σ (A x)‖ :=
      ZeroHomClass.bound_of_antilipschitz ((coordProjectionL σ).comp A) hanti x
    have hdiff : ‖coordProjectionL σ (A x) - coordProjectionL σ (B x)‖ ≤ δ * ‖x‖ := by
      rw [norm_sub_rev]
      exact (((coordProjectionL σ).comp B - (coordProjectionL σ).comp A).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hB.le (norm_nonneg x))
    have htri : ‖coordProjectionL σ (A x)‖ ≤ ‖coordProjectionL σ (B x)‖ + δ * ‖x‖ :=
      (norm_le_norm_add_norm_sub (coordProjectionL σ (B x))
        (coordProjectionL σ (A x))).trans (by
          gcongr
          simpa only [norm_sub_rev] using hdiff)
    have hm := mul_le_mul_of_nonneg_left htri hKr.le
    have hc : (K : ℝ) * (δ * ‖x‖) = (1 / 2 : ℝ) * ‖x‖ := by
      rw [← mul_assoc, hKδ]
    simp only [mul_add, hc] at hm
    change ‖x‖ ≤ (2 * (K : ℝ)) * _
    nlinarith

/-- One finite constant works for a suitable coordinate projection of every
orthonormal m-frame in R^N. No optimal numerical constant is required. -/
theorem uniform_isometric_coordinate_bound (m N : ℕ) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ A ∈ isometricOperators m N,
      ∃ σ : Fin m ↪ Fin N, ∀ x, ‖x‖ ≤ (K : ℝ) * ‖coordProjectionL σ (A x)‖ := by
  classical
  have hinj (A : isometricOperators m N) : Injective A.val := by
    let L : Euclid m →ₗᵢ[ℝ] Euclid N :=
      { A.val.toLinearMap with norm_map' := A.property }
    exact L.injective
  choose σ K U hK hU hmem hbound using
    (fun A : isometricOperators m N => exists_coordinate_bound_neighborhood A.val (hinj A))
  obtain ⟨q, hq⟩ := (isCompact_isometricOperators m N).elim_finite_subcover U hU (by
    intro A hA
    exact mem_iUnion.mpr ⟨⟨A, hA⟩, hmem ⟨A, hA⟩⟩)
  refine ⟨1 + q.sup K, by positivity, ?_⟩
  intro A hA
  obtain ⟨B, hBq, hBU⟩ := mem_iUnion₂.mp (hq hA)
  refine ⟨σ B, fun x => (hbound B A hBU x).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact_mod_cast (Finset.le_sup hBq).trans (le_add_self : q.sup K ≤ 1 + q.sup K)

#print axioms isCompact_isometricOperators
#print axioms exists_coordinate_bound_neighborhood
#print axioms uniform_isometric_coordinate_bound
#assert_trust kernel isCompact_isometricOperators
#assert_trust kernel exists_coordinate_bound_neighborhood
#assert_trust kernel uniform_isometric_coordinate_bound

end NLA.TR06.Area.Proposed
