/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original projective counterexample: Matthew J. Colbrook.
-/
import NLA.TR27.Algebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The integral coordinate map of the projected curve

The homogeneous coordinate functions make both parameters integral over their
coordinate image. Lying over and the complex Nullstellensatz then identify the
whole affine zero locus with the parameter image. This supplies the algebraic
image bridge for the projective rank argument; it is not that rank argument.
-/

set_option autoImplicit false

noncomputable section
namespace NLA.TR27

local instance coordinateAlgebra : Algebra CoordinatePolynomial ParameterPolynomial :=
  (coordinateSubstitution : CoordinatePolynomial →+* ParameterPolynomial).toAlgebra

private theorem coordinate_algebraMap : algebraMap CoordinatePolynomial ParameterPolynomial =
    (coordinateSubstitution : CoordinatePolynomial →+* ParameterPolynomial) := rfl

private theorem integral_constant (c : ℂ) :
    IsIntegral CoordinatePolynomial (MvPolynomial.C c : ParameterPolynomial) := by
  simpa [coordinate_algebraMap, coordinateSubstitution] using
    (isIntegral_algebraMap (R := CoordinatePolynomial) (A := ParameterPolynomial)
      (x := MvPolynomial.C c))

private theorem integral_coordinate (j : Fin 12) :
    IsIntegral CoordinatePolynomial (homogeneousCoordinate j) := by
  simpa [coordinate_algebraMap, coordinateSubstitution] using
    (isIntegral_algebraMap (R := CoordinatePolynomial) (A := ParameterPolynomial)
      (x := MvPolynomial.X j))

/-- The first parameter's twelfth power satisfies an exact monic quadratic. -/
theorem parameter_zero_power_integral :
    IsIntegral CoordinatePolynomial ((MvPolynomial.X (0 : Fin 2) : ParameterPolynomial) ^ 12) := by
  let A : CoordinatePolynomial := MvPolynomial.C (1 / 85 : ℂ) *
    (MvPolynomial.C 8 * MvPolynomial.X 0 + MvPolynomial.C 9 * MvPolynomial.X 1)
  let B : CoordinatePolynomial := MvPolynomial.C (-5 / 85 : ℂ) * MvPolynomial.X 0 ^ 2
  refine ⟨Polynomial.X ^ 2 + (Polynomial.C A * Polynomial.X + Polynomial.C B), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    compute_degree
    norm_num
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    rw [coordinate_algebraMap]
    apply MvPolynomial.funext
    intro w
    norm_num [coordinateSubstitution, A, B,
      homogeneousCoordinate, coordinateIndex, powerSum, Fin.ext_iff]
    ring

/-- The mixed monomial is recovered from the first homogeneous coordinate. -/
theorem parameter_mixed_integral :
    IsIntegral CoordinatePolynomial
      ((MvPolynomial.X (0 : Fin 2) : ParameterPolynomial) ^ 11 * MvPolynomial.X 1) := by
  have h := (integral_constant (1 / 3)).mul
    (((integral_constant 5).mul parameter_zero_power_integral).sub (integral_coordinate 0))
  convert h using 1 <;> try rfl
  apply MvPolynomial.funext
  intro w
  norm_num [homogeneousCoordinate, coordinateIndex, powerSum, Fin.ext_iff]
  ring

/-- The infinity coordinate recovers the second parameter's twelfth power. -/
theorem parameter_one_power_integral :
    IsIntegral CoordinatePolynomial ((MvPolynomial.X (1 : Fin 2) : ParameterPolynomial) ^ 12) := by
  have h := (integral_constant (1 / 5)).mul
    ((integral_coordinate 11).add ((integral_constant 535538).mul parameter_mixed_integral))
  convert h using 1 <;> try rfl
  apply MvPolynomial.funext
  intro w
  norm_num [homogeneousCoordinate, coordinateIndex, powerSum, Fin.ext_iff]
  ring

/-- Each parameter is integral, by its positive twelfth power. -/
theorem parameter_integral (j : Fin 2) :
    IsIntegral CoordinatePolynomial (MvPolynomial.X j : ParameterPolynomial) := by
  fin_cases j
  · exact IsIntegral.of_pow (by decide : 0 < 12) parameter_zero_power_integral
  · exact IsIntegral.of_pow (by decide : 0 < 12) parameter_one_power_integral

/-- The complete polynomial substitution map is integral, not just its generators. -/
theorem substitution_integral :
    (coordinateSubstitution : CoordinatePolynomial →+* ParameterPolynomial).IsIntegral := by
  intro p
  -- The induced algebra has exactly the substitution as its structural map.
  change IsIntegral CoordinatePolynomial p
  induction p using MvPolynomial.induction_on with
  | C c => exact integral_constant c
  | add p q hp hq => exact hp.add hq
  | mul_X p j hp => exact hp.mul (parameter_integral j)

/-- Evaluation commutes with the frozen homogeneous substitution. -/
theorem eval_coordinateSubstitution (u : ParameterSpace) (p : CoordinatePolynomial) :
    MvPolynomial.eval u (coordinateSubstitution p) =
      MvPolynomial.eval (homogeneousMap u) p := by
  exact MvPolynomial.comp_aeval_apply homogeneousCoordinate (MvPolynomial.aeval u) p

/-- Every homogeneous image point satisfies all equations in the kernel ideal. -/
theorem homogeneousMap_mem_zeroLocus (u : ParameterSpace) :
    homogeneousMap u ∈ MvPolynomial.zeroLocus ℂ witnessIdeal := by
  intro p hp
  change coordinateSubstitution p = 0 at hp
  change MvPolynomial.eval (homogeneousMap u) p = 0
  rw [← eval_coordinateSubstitution, hp, map_zero]

/-- The concrete homogeneous parameter map takes values in the whole witness cone. -/
theorem homogeneousMap_mem_cone (u : ParameterSpace) :
    homogeneousMap u ∈ witnessVariety.cone :=
  homogeneousMap_mem_zeroLocus u

/-- Integrality and lying-over show that the parameter image is the complete zero locus. -/
theorem zeroLocus_eq_range_homogeneousMap :
    MvPolynomial.zeroLocus ℂ witnessIdeal = Set.range homogeneousMap := by
  let : Algebra.IsIntegral CoordinatePolynomial ParameterPolynomial :=
    ⟨substitution_integral⟩
  apply Set.Subset.antisymm
  · intro w hw
    let M : Ideal CoordinatePolynomial := MvPolynomial.vanishingIdeal ℂ {w}
    have hM : M.IsMaximal := inferInstance
    have hker : RingHom.ker (algebraMap CoordinatePolynomial ParameterPolynomial) ≤ M := by
      intro p hp
      change p ∈ witnessIdeal at hp
      simpa only [M, MvPolynomial.mem_vanishingIdeal_iff, Set.mem_singleton_iff,
        forall_eq] using hw p hp
    obtain ⟨N, hN, hcomap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral M hker
    obtain ⟨u, hu⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hN
    refine ⟨u, ?_⟩
    funext j
    have hj : MvPolynomial.X j - MvPolynomial.C (w j) ∈ M := by
      simp [M]
    rw [← hcomap] at hj
    change algebraMap CoordinatePolynomial ParameterPolynomial
      (MvPolynomial.X j - MvPolynomial.C (w j)) ∈ N at hj
    rw [hu] at hj
    have heval := (MvPolynomial.mem_vanishingIdeal_iff.mp hj) u (Set.mem_singleton u)
    change MvPolynomial.eval u (coordinateSubstitution
      (MvPolynomial.X j - MvPolynomial.C (w j))) = 0 at heval
    rw [eval_coordinateSubstitution] at heval
    simpa only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero] using heval
  · rintro w ⟨u, rfl⟩
    exact homogeneousMap_mem_zeroLocus u

/-- The parameter map is homogeneous of degree twelve, including at zero. -/
theorem homogeneousMap_smul (a : ℂ) (u : ParameterSpace) :
    homogeneousMap (a • u) = a ^ 12 • homogeneousMap u := by
  ext j
  fin_cases j <;>
    norm_num [homogeneousMap_apply, coordinateIndex, powerSum, Fin.ext_iff,
      Pi.smul_apply, smul_eq_mul] <;> ring

/-- All scalars and both projective charts are in the parameter image. -/
theorem range_homogeneousMap_eq_parameterizedCone :
    Set.range homogeneousMap = parameterizedCone := by
  apply Set.Subset.antisymm
  · rintro w ⟨u, rfl⟩
    by_cases h0 : u 0 = 0
    · have hu : u = u 1 • (![0, 1] : ParameterSpace) := by
        ext j
        fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul, h0]
      rw [hu, homogeneousMap_smul, homogeneousMap_infinity]
      by_cases h1 : u 1 = 0
      · left
        simp [h1]
      · right
        exact ⟨u 1 ^ 12, pow_ne_zero _ h1, none, rfl⟩
    · have hu : u = u 0 • (![1, u 1 / u 0] : ParameterSpace) := by
        ext j
        fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul]
        field_simp
      rw [hu, homogeneousMap_smul, homogeneousMap_one]
      right
      exact ⟨u 0 ^ 12, pow_ne_zero _ h0, some (u 1 / u 0), rfl⟩
  · rintro w (rfl | ⟨a, ha, t, rfl⟩)
    · exact ⟨(0 : ℂ) • (![0, 1] : ParameterSpace), by rw [homogeneousMap_smul]; simp⟩
    · obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a (by decide : 0 < 12)
      obtain ⟨u, hu⟩ := curve_mem_range_homogeneousMap t
      exact ⟨b • u, by rw [homogeneousMap_smul, hb, hu]⟩

/-- The complete zero locus and the exhaustive scalar/projective parameterization agree. -/
theorem whole_closed_image :
    MvPolynomial.zeroLocus ℂ witnessIdeal = Set.range homogeneousMap ∧
      witnessVariety.cone = parameterizedCone := by
  refine ⟨zeroLocus_eq_range_homogeneousMap, ?_⟩
  change MvPolynomial.zeroLocus ℂ witnessIdeal = parameterizedCone
  rw [zeroLocus_eq_range_homogeneousMap, range_homogeneousMap_eq_parameterizedCone]

end NLA.TR27
