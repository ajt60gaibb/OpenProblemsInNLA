/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.FiniteCharactersDefinitions
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Set TopologicalSpace
namespace NLA.TR06.Proposed

/-- Finite actual algebraically closed field-valued characters imply module
finiteness for a finite-type algebra, retaining all nilpotents. -/
theorem finite_algebra_of_finite_characters : FiniteAlgebraOfFiniteCharactersStatement := by
  classical
  intro K A _ _ _ _ _ hcharacters
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  let characterPrime : (A →ₐ[K] K) → PrimeSpectrum A := fun f =>
    ⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime f.toRingHom⟩
  have hclosed : (closedPoints (PrimeSpectrum A)).Finite := by
    apply (hcharacters.image characterPrime).subset
    intro p hp
    let : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hp
    let : Field (A ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
    let : Module.Finite K (A ⧸ p.asIdeal) :=
      finite_of_finite_type_of_isJacobsonRing K (A ⧸ p.asIdeal)
    let lift : (A ⧸ p.asIdeal) →ₐ[K] K := IsAlgClosed.lift
    let f : A →ₐ[K] K := lift.comp (Ideal.Quotient.mkₐ K p.asIdeal)
    refine ⟨f, mem_univ _, ?_⟩
    apply PrimeSpectrum.ext
    change RingHom.ker (lift.toRingHom.comp (Ideal.Quotient.mk p.asIdeal)) = p.asIdeal
    rw [RingHom.ker_comp_of_injective _ lift.injective, Ideal.mk_ker]
  let : DiscreteTopology (PrimeSpectrum A) := JacobsonSpace.discreteTopology hclosed
  have hdim : Ring.KrullDimLE 0 A :=
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).2
  exact (Module.finite_iff_krullDimLE_zero K A).mpr hdim

#print axioms finite_algebra_of_finite_characters
#assert_trust kernel finite_algebra_of_finite_characters
end NLA.TR06.Proposed
