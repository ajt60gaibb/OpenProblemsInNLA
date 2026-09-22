/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original projective counterexample: Matthew J. Colbrook.
-/
import NLA.TR27.IntegralImage
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Geometry of the complete projected curve

This module establishes the concrete projective-variety hypotheses from the
frozen polynomial ideal and full image. No rank or independence conclusion is
assumed in those hypotheses.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.TR27
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every coordinate has the same degree twelve, with no exceptional chart. -/
theorem homogeneousCoordinate_isHomogeneous (j : Fin 12) :
    (homogeneousCoordinate j).IsHomogeneous 12 := by
  unfold homogeneousCoordinate
  apply MvPolynomial.IsHomogeneous.sub
  · have h := (MvPolynomial.isHomogeneous_C_mul_X_pow (5 : ℂ)
      (0 : Fin 2) (12 - (coordinateIndex j : ℕ))).mul
      (MvPolynomial.isHomogeneous_X_pow (1 : Fin 2) (coordinateIndex j : ℕ))
    have hi : (coordinateIndex j : ℕ) ≤ 12 := Nat.le_of_lt_succ (coordinateIndex j).isLt
    simpa [Nat.sub_add_cancel hi] using h
  · simpa using (MvPolynomial.isHomogeneous_C_mul_X_pow
      (powerSum (coordinateIndex j : ℕ)) (0 : Fin 2) 11).mul
      (MvPolynomial.isHomogeneous_X (R := ℂ) (1 : Fin 2))

/-- The monic-coordinate consequences force a zero parameter whenever the image is zero. -/
theorem homogeneousMap_eq_zero_iff (u : ParameterSpace) :
    homogeneousMap u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hquadratic := integral_quadratic u
    rw [h] at hquadratic
    have hu0 : u 0 = 0 := by
      norm_num only [Pi.zero_apply, zero_mul, add_zero, mul_zero, zero_pow, sub_zero] at hquadratic
      rcases mul_eq_zero.mp hquadratic with hc | hx
      · norm_num at hc
      · exact eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero hx)
    have hlast := congrFun h 11
    norm_num [homogeneousMap_apply, coordinateIndex, Fin.ext_iff, hu0] at hlast
    have hu1 : u 1 = 0 := hlast
    ext j
    fin_cases j <;> simp [hu0, hu1]
  · rintro rfl
    have h := homogeneousMap_smul (0 : ℂ) (0 : ParameterSpace)
    simpa using h

/-- Exact frozen homogeneous semantics, including basepoint-freeness and the whole scalar parameterization. -/
theorem homogeneous_parameter_semantics :
    (∀ j, (homogeneousCoordinate j).IsHomogeneous 12) ∧
    (∀ u : ParameterSpace, homogeneousMap u = 0 ↔ u = 0) ∧
    Set.range homogeneousMap = parameterizedCone :=
  ⟨homogeneousCoordinate_isHomogeneous, homogeneousMap_eq_zero_iff,
    range_homogeneousMap_eq_parameterizedCone⟩

/-- Substitution multiplies homogeneous degrees by twelve. -/
theorem substitution_homogeneous {p : CoordinatePolynomial} {n : ℕ}
    (hp : p.IsHomogeneous n) : (coordinateSubstitution p).IsHomogeneous (12 * n) := by
  exact hp.aeval homogeneousCoordinate homogeneousCoordinate_isHomogeneous

/-- Homogeneous components of different degrees cannot cancel after substitution. -/
theorem substitution_homogeneousComponent (p : CoordinatePolynomial) (n : ℕ) :
    MvPolynomial.homogeneousComponent (12 * n) (coordinateSubstitution p) =
      coordinateSubstitution (MvPolynomial.homogeneousComponent n p) := by
  have hsum : coordinateSubstitution p =
      ∑ i ∈ Finset.range (p.totalDegree + 1),
        coordinateSubstitution (MvPolynomial.homogeneousComponent i p) := by
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
  rw [hsum, map_sum]
  simp_rw [MvPolynomial.homogeneousComponent_of_mem
    (substitution_homogeneous (MvPolynomial.homogeneousComponent_isHomogeneous _ _))]
  simp only [Nat.mul_left_cancel_iff (by decide : 0 < 12)]
  by_cases hn : n < p.totalDegree + 1
  · simp [hn]
  · have hp : p.totalDegree < n := by omega
    simp [hn, MvPolynomial.homogeneousComponent_eq_zero n p hp]

/-- The defining kernel is homogeneous in the ordinary total-degree grading. -/
theorem witnessIdeal_isHomogeneous :
    witnessIdeal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 12) ℂ) := by
  intro n p hp
  rw [← DirectSum.Decomposition.decompose'_eq, MvPolynomial.decomposition.decompose'_apply]
  change coordinateSubstitution (MvPolynomial.homogeneousComponent n p) = 0
  change coordinateSubstitution p = 0 at hp
  rw [← substitution_homogeneousComponent, hp, map_zero]

/-- The target polynomial domain makes the kernel prime. -/
theorem witnessIdeal_isPrime : witnessIdeal.IsPrime :=
  RingHom.ker_isPrime (coordinateSubstitution : CoordinatePolynomial →+* ParameterPolynomial)

/-- Finite parameters alone already span the source space. -/
theorem sourceCurve_span :
    Submodule.span ℂ (Set.range (fun i : Fin 13 => sourceCurve (some (i : ℂ)))) = ⊤ := by
  have hi : Function.Injective (fun i : Fin 13 => (i : ℂ)) := by
    intro i j h
    exact Fin.ext (Nat.cast_injective h)
  have hind := Matrix.linearIndependent_rows_of_det_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr hi)
  apply hind.span_eq_top_of_card_eq_finrank'
  simp

/-- Every curve point, including infinity, belongs to the complete cone. -/
theorem curve_mem_cone (t : Option ℂ) : curve t ∈ witnessVariety.cone := by
  obtain ⟨u, hu⟩ := curve_mem_range_homogeneousMap t
  rw [← hu]
  exact homogeneousMap_mem_cone u

/-- Surjective projection of the source spanning family gives nondegeneracy. -/
theorem witness_cone_span : Submodule.span ℂ witnessVariety.cone = ⊤ := by
  have hmap := congrArg (Submodule.map quotientLinearMap) sourceCurve_span
  rw [Submodule.map_span, Submodule.map_top,
    LinearMap.range_eq_top.mpr quotientMap_surjective] at hmap
  apply top_unique
  rw [← hmap]
  apply Submodule.span_le.mpr
  rintro w ⟨u, ⟨i, rfl⟩, rfl⟩
  exact Submodule.subset_span (curve_mem_cone (some (i : ℂ)))

/-- The full frozen homogeneous ideal satisfies every classical variety hypothesis. -/
theorem witness_admissible : witnessVariety.Admissible := by
  let : witnessIdeal.IsPrime := witnessIdeal_isPrime
  refine ⟨witnessIdeal_isHomogeneous, witnessIdeal_isPrime, ?_, ?_, witness_cone_span⟩
  · change IsReduced (CoordinatePolynomial ⧸ witnessIdeal)
    infer_instance
  · exact ⟨curve (some 0), curve_mem_cone (some 0), curve_nonzero (some 0)⟩

end NLA.TR27
