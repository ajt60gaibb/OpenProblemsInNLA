/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Original TR-06 mathematical proof attribution: Matthew J. Colbrook.

Exact intermediate statements independently reviewed before implementation.
-/
import NLA.TR06.GenericUnramifiedDefinitions
import Mathlib.RingTheory.Algebraic.Integral

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Function Set

namespace NLA.TR06.Proposed

/-- The actual generic residue-field extension is finite by quasi-finiteness,
then separable in characteristic zero, giving unramifiedness at the zero prime. -/
theorem generic_unramified_at : GenericUnramifiedAtStatement := by
  intro R S _ _ _ _ _ _ _ hinj hqf
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  let : Algebra.QuasiFiniteAt R (⊥ : Ideal S) := hqf
  let := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal R) (⊥ : Ideal S)
  let : Module.Finite (⊥ : Ideal R).ResidueField (⊥ : Ideal S).ResidueField := inferInstance
  let : CharZero (⊥ : Ideal R).ResidueField := IsFractionRing.charZero_of_isFractionRing R
  apply (Algebra.isUnramifiedAt_iff_map_eq R (⊥ : Ideal R) (⊥ : Ideal S)).mpr
  refine ⟨inferInstance, ?_⟩
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot, Ideal.map_bot]

/-- The unramified source denominator can be replaced by a nonzero base
multiple using the finite Zariski Main envelope and an integral relation. -/
theorem generic_unramified_localization : GenericUnramifiedLocalizationStatement := by
  classical
  intro R S _ _ _ _ _ _ _ hinj hqf
  let : Algebra.QuasiFiniteAt R (⊥ : Ideal S) := hqf
  let : Algebra.IsUnramifiedAt R (⊥ : Ideal S) := generic_unramified_at R S hinj hqf
  obtain ⟨s, hs, hunram⟩ :=
    Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := R) (⊥ : Ideal S)
  have hs0 : s ≠ 0 := by simpa using hs
  obtain ⟨A, hA, t, ht, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := R) (⊥ : Ideal S)
  let : Module.Finite R A := ⟨(Submodule.fg_top A.toSubmodule).mpr hA⟩
  have ht0 : t.val ≠ 0 := by simpa using ht
  obtain ⟨a, m, ha⟩ := Localization.awayMap_surjective_iff.mp hbij.surjective s
  have haval : a.val = t.val ^ m * s := ha
  have ha0 : a ≠ 0 := by
    intro h
    have hval : a.val = 0 := congrArg Subtype.val h
    exact (mul_ne_zero (pow_ne_zero m ht0) hs0) (haval.symm.trans hval)
  obtain ⟨r, hr, hdiv⟩ := (IsIntegral.of_finite R a).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ha0)
  have hsr : s ∣ algebraMap R S r := by
    have hsaval : s ∣ a.val := ⟨t.val ^ m, by rw [haval, mul_comm]⟩
    have hmap : a.val ∣ algebraMap R S r := by
      simpa only [AlgHom.commutes, Subalgebra.val_apply] using (map_dvd A.val hdiv)
    exact hsaval.trans hmap
  have hsub : (↑(PrimeSpectrum.basicOpen (algebraMap R S r)) : Set (PrimeSpectrum S)) ⊆
      Algebra.unramifiedLocus R S := by
    apply Subset.trans ?_ (Algebra.basicOpen_subset_unramifiedLocus_iff.mpr hunram)
    intro p hp
    change algebraMap R S r ∉ p.asIdeal at hp
    change s ∉ p.asIdeal
    intro hsp
    obtain ⟨b, hb⟩ := hsr
    apply hp
    rw [hb]
    exact p.asIdeal.mul_mem_right b hsp
  let : Algebra.FormallyUnramified R (Localization.Away (algebraMap R S r)) :=
    Algebra.basicOpen_subset_unramifiedLocus_iff.mp hsub
  refine ⟨r, hr, ?_⟩
  let Sr := Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers r))
  let : IsLocalization.Away (algebraMap R S r) Sr := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers r)) Sr)
  let e : Localization.Away (algebraMap R S r) ≃ₐ[S] Sr :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap R S r)) _ _
  let : Algebra.FormallyUnramified R Sr :=
    Algebra.FormallyUnramified.of_equiv (e.restrictScalars R)
  exact Algebra.FormallyUnramified.of_restrictScalars R (Localization.Away r) Sr

#print axioms generic_unramified_at
#print axioms generic_unramified_localization
#assert_trust kernel generic_unramified_at
#assert_trust kernel generic_unramified_localization

end NLA.TR06.Proposed
