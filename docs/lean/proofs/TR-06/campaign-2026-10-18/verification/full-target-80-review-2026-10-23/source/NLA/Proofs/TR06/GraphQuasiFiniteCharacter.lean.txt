/-
Copyright (c) 2026. Released under Apache 2.0 license.
Explicit character residue-field identification and pointwise quasi-finiteness.
-/
import NLA.Proofs.TR06.GraphQuasiFiniteCotangent

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped TensorProduct
namespace NLA.Proofs.TR06.GraphQuasiFinite

attribute [local instance] RingHom.ker_isPrime

/-- A genuinely surjective character identifies its actual residue field with
the target field, as an algebra over the source ring. -/
def residueCharacterEquiv {S K : Type*} [CommRing S] [Field K] [Algebra S K]
    (hsurj : Function.Surjective (algebraMap S K)) :
    (RingHom.ker (algebraMap S K)).ResidueField ≃ₐ[S] K := by
  let q := RingHom.ker (algebraMap S K)
  have hu : q.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap S K) := by
    intro s hs
    change IsUnit ((algebraMap S K) s)
    exact isUnit_iff_ne_zero.mpr hs
  let f : q.ResidueField →ₐ[S] K :=
    Ideal.ResidueField.liftₐ q (Algebra.ofId S K) le_rfl hu
  apply AlgEquiv.ofBijective f
  refine ⟨RingHom.injective f.toRingHom, ?_⟩
  intro a
  obtain ⟨s,hs⟩ := hsurj a
  refine ⟨algebraMap S q.ResidueField s, ?_⟩
  exact (f.commutes s).trans hs

/-- Relative derivation vanishing at an actual surjective character forces
actual unramifiedness at its actual kernel prime. -/
theorem isUnramifiedAt_character_of_derivations
    {R S K : Type*} [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra S K] [Algebra R K] [IsScalarTower R S K]
    [Algebra.EssFiniteType R S]
    (hsurj : Function.Surjective (algebraMap S K))
    (hD : ∀ D : Derivation R S K, D = 0) :
    Algebra.IsUnramifiedAt R (RingHom.ker (algebraMap S K)) := by
  have hf := cotangent_fiber_subsingleton_of_derivations hD
  let e := (residueCharacterEquiv hsurj).toLinearEquiv.rTensor (KaehlerDifferential R S)
  have hr : Subsingleton ((RingHom.ker (algebraMap S K)).ResidueField ⊗[S]
      KaehlerDifferential R S) := e.subsingleton_congr.mpr hf
  exact isUnramifiedAt_of_cotangent_fiber_subsingleton _ hr

/-- The actual local quasi-finiteness consequence, under the same genuine
finite-type and character hypotheses. -/
theorem quasiFiniteAt_character_of_derivations
    {R S K : Type*} [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra S K] [Algebra R K] [IsScalarTower R S K]
    [Algebra.EssFiniteType R S]
    (hsurj : Function.Surjective (algebraMap S K))
    (hD : ∀ D : Derivation R S K, D = 0) :
    Algebra.QuasiFiniteAt R (RingHom.ker (algebraMap S K)) := by
  let : Algebra.IsUnramifiedAt R (RingHom.ker (algebraMap S K)) :=
    isUnramifiedAt_character_of_derivations hsurj hD
  infer_instance

#print axioms residueCharacterEquiv
#print axioms isUnramifiedAt_character_of_derivations
#print axioms quasiFiniteAt_character_of_derivations
#assert_trust kernel residueCharacterEquiv
#assert_trust kernel isUnramifiedAt_character_of_derivations
#assert_trust kernel quasiFiniteAt_character_of_derivations
end NLA.Proofs.TR06.GraphQuasiFinite
