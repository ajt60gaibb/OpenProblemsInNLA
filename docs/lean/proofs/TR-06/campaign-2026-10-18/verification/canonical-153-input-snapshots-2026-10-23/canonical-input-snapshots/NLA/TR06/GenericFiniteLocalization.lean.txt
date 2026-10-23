/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.

The exact intermediate statement was independently reviewed before implementation.
Generic-point quasi-finiteness is a premise, not a conclusion about tensor fibers.
-/
import NLA.TR06.GenericFiniteLocalizationDefinitions
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Algebra

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Function

namespace NLA.TR06.Proposed

/-- Quasi-finiteness at the generic point becomes finiteness after inverting a
nonzero element of the base domain, using the canonical localized scalar action. -/
theorem generic_finite_localization : GenericFiniteLocalizationStatement := by
  classical
  intro R S _ _ _ _ _ _ _hinj hqf
  let : Algebra.QuasiFiniteAt R (⊥ : Ideal S) := hqf
  obtain ⟨A, hA, t, ht, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := R) (⊥ : Ideal S)
  let : Module.Finite R A := ⟨(Submodule.fg_top A.toSubmodule).mpr hA⟩
  have ht0 : t ≠ 0 := by simpa using ht
  obtain ⟨r, hr, hdiv⟩ := (IsIntegral.of_finite R t).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ht0)
  have hsurj := (Localization.awayMap_bijective_of_dvd A.val.toRingHom hdiv hbij).surjective
  refine ⟨r, hr, ?_⟩
  let Rr := Localization.Away r
  let Ar := Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers r))
  let Sr := Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers r))
  let : Module.Finite Rr Ar := Module.Finite.of_isLocalization R A (Submonoid.powers r)
  let : IsLocalization.Away (algebraMap R A r) Ar := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers r)) Ar)
  let : IsLocalization.Away (A.val.toRingHom (algebraMap R A r)) Sr := by
    have hval : A.val.toRingHom (algebraMap R A r) = algebraMap R S r := A.val.commutes r
    rw [hval]
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers r)) Sr)
  let f : Ar →ₐ[Rr] Sr := IsLocalization.mapₐ (Submonoid.powers r) Rr Ar Sr A.val
  have hf : f.toRingHom = IsLocalization.Away.map Ar Sr A.val.toRingHom (algebraMap R A r) := by
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid A (Submonoid.powers r))
    simp [f, IsLocalization.mapₐ, IsLocalization.Away.map, IsLocalization.map_comp]
  have hfsurj : Surjective f := by
    change Surjective f.toRingHom
    rw [hf, IsLocalization.Away.map_surjective_iff]
    exact Localization.awayMap_surjective_iff.mp hsurj
  exact Module.Finite.of_surjective f.toLinearMap hfsurj

#print axioms generic_finite_localization
#assert_trust kernel generic_finite_localization

end NLA.TR06.Proposed
