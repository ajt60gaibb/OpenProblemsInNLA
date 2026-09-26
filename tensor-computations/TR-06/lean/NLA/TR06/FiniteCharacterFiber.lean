/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.

The exact three intermediate statements were independently reviewed before proof.
Original TR-06 mathematical proof attribution: Matthew J. Colbrook.
-/
import NLA.TR06.FiniteCharacterFiberDefinitions
import NLA.TR06.FiniteCharacters

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Function Set

namespace NLA.TR06.Proposed

/-- The quotient character map is the prescribed precomposition and has exactly
as image the original characters that restrict to the given base character. -/
theorem quotient_character_correspondence : QuotientCharacterCorrespondenceStatement := by
  intro K R S _ _ _ _ _ _ _ χ
  let J := characterFiberIdeal (S := S) χ
  refine ⟨?_, ?_, ?_⟩
  · intro f _
    change (f.comp (Ideal.Quotient.mkₐ K J)).comp (IsScalarTower.toAlgHom K R S) = χ
    ext r
    have hm : algebraMap R S (r - algebraMap K R (χ r)) ∈ J := by
      apply Ideal.mem_map_of_mem
      simp [RingHom.mem_ker]
    have heq : Ideal.Quotient.mk J (algebraMap R S r) =
        Ideal.Quotient.mk J (algebraMap K S (χ r)) := by
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      simpa only [map_sub, ← IsScalarTower.algebraMap_apply K R S] using hm
    change f (Ideal.Quotient.mk J (algebraMap R S r)) = χ r
    rw [heq]
    exact f.commutes (χ r)
  · intro f _ g _ hfg
    ext x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_fun hfg s
  · intro f hf
    have hJ : J ≤ RingHom.ker f.toRingHom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change f (algebraMap R S r) = 0
      have hfr : f (algebraMap R S r) = χ r := DFunLike.congr_fun hf r
      rw [hfr]
      exact RingHom.mem_ker.mp hr
    let g := Ideal.Quotient.liftₐ J f (fun s hs => RingHom.mem_ker.mp (hJ hs))
    exact ⟨g, mem_univ _, Ideal.Quotient.liftₐ_comp J f _⟩

/-- Finite actual characters in a fiber give genuine quasi-finiteness at each
source-character prime, retaining nilpotents in the quotient fiber algebra. -/
theorem quasiFiniteAt_of_finite_character_fiber : QuasiFiniteAtOfFiniteCharacterFiberStatement := by
  classical
  intro K R S _ _ _ _ _ _ _ _ _ χ hfin f hf
  let q := RingHom.ker f.toRingHom
  let : q.IsPrime := RingHom.ker_isPrime f.toRingHom
  let J := characterFiberIdeal (S := S) χ
  have hquot : (Set.univ : Set ((S ⧸ J) →ₐ[K] K)).Finite :=
    (quotient_character_correspondence K R S χ).finite_iff_finite.mpr hfin
  let : Module.Finite K (S ⧸ J) := finite_algebra_of_finite_characters K (S ⧸ J) hquot
  let : Module.Finite R (S ⧸ J) := Module.Finite.of_restrictScalars_finite K R (S ⧸ J)
  have hunder : q.under R = RingHom.ker χ.toRingHom := by
    ext r
    change f (algebraMap R S r) = 0 ↔ χ r = 0
    rw [show f (algebraMap R S r) = χ r from DFunLike.congr_fun hf r]
  have hideal : (q.under R).map (algebraMap R S) = J :=
    congrArg (fun I : Ideal R => I.map (algebraMap R S)) hunder
  let : Module.Finite R (S ⧸ (q.under R).map (algebraMap R S)) := by
    rw [hideal]
    infer_instance
  let : Algebra.WeaklyQuasiFiniteAt R q := by
    dsimp only [Algebra.WeaklyQuasiFiniteAt, Algebra.QuasiFiniteAt]
    infer_instance
  let : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType K R S
  exact Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt q

/-- A finite nonempty actual character fiber controls the source generic point
when the source algebra is a domain. -/
theorem generic_quasiFinite_of_finite_nonempty_character_fiber :
    GenericQuasiFiniteOfFiniteNonemptyCharacterFiberStatement := by
  intro K R S _ _ _ _ _ _ _ _ _ _ χ hfin hnonempty
  obtain ⟨f, hf⟩ := hnonempty
  let : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom
  let : Algebra.QuasiFiniteAt R (RingHom.ker f.toRingHom) :=
    quasiFiniteAt_of_finite_character_fiber K R S χ hfin f hf
  exact Algebra.QuasiFiniteAt.of_le (R := R) (Q := RingHom.ker f.toRingHom) bot_le

#print axioms quotient_character_correspondence
#print axioms quasiFiniteAt_of_finite_character_fiber
#print axioms generic_quasiFinite_of_finite_nonempty_character_fiber
#assert_trust kernel quotient_character_correspondence
#assert_trust kernel quasiFiniteAt_of_finite_character_fiber
#assert_trust kernel generic_quasiFinite_of_finite_nonempty_character_fiber

end NLA.TR06.Proposed
