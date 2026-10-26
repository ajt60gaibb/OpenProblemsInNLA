/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual complex point derivations, with canonical base-character compatibility,
imply local quasi-finiteness. Real setwise local injectivity is not a premise.
-/
import NLA.Proofs.TR06.GraphQuasiFiniteCharacter

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.GraphQuasiFinite

attribute [local instance] RingHom.ker_isPrime

/-- The exact point-derivation criterion for an actual complex character.
The base character and its compatibility are explicit. -/
theorem isUnramifiedAt_of_point_derivations
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] [Algebra R S] [IsScalarTower ℂ R S]
    [Algebra.FiniteType R S]
    (χ : S →ₐ[ℂ] ℂ) (ψ : R →ₐ[ℂ] ℂ)
    (hcompat : χ.comp (IsScalarTower.toAlgHom ℂ R S) = ψ)
    (hzero : ∀ δ : S →ₗ[ℂ] ℂ,
      (∀ a b, δ (a*b) = χ a * δ b + χ b * δ a) →
      (∀ b : R, δ (algebraMap R S b) = 0) → δ = 0) :
    Algebra.IsUnramifiedAt R (RingHom.ker χ.toRingHom) := by
  let : Algebra S ℂ := χ.toRingHom.toAlgebra
  let : Algebra R ℂ := ψ.toRingHom.toAlgebra
  let : IsScalarTower ℂ S ℂ := IsScalarTower.of_algebraMap_eq
    (fun c => (χ.commutes c).symm)
  let : IsScalarTower ℂ R ℂ := IsScalarTower.of_algebraMap_eq
    (fun c => (ψ.commutes c).symm)
  let : IsScalarTower R S ℂ := IsScalarTower.of_algebraMap_eq
    (fun b => (AlgHom.congr_fun hcompat b).symm)
  have hsurj : Function.Surjective (algebraMap S ℂ) := by
    intro c
    exact ⟨algebraMap ℂ S c, χ.commutes c⟩
  apply isUnramifiedAt_character_of_derivations hsurj
  intro D
  let δ : S →ₗ[ℂ] ℂ := D.toLinearMap.restrictScalars ℂ
  have hδ : δ = 0 := hzero δ (by
    intro a b
    change D (a*b) = χ a * D b + χ b * D a
    exact D.leibniz a b) (by
    intro b
    exact D.map_algebraMap b)
  apply Derivation.ext
  intro s
  exact LinearMap.congr_fun hδ s

/-- Actual complex relative tangent-rank information yields genuine algebraic
quasi-finiteness at the character prime, including singular/nonreduced source
algebras. No real topological isolation or fiber-finiteness assumption is used. -/
theorem quasiFiniteAt_of_point_derivations
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] [Algebra R S] [IsScalarTower ℂ R S]
    [Algebra.FiniteType R S]
    (χ : S →ₐ[ℂ] ℂ) (ψ : R →ₐ[ℂ] ℂ)
    (hcompat : χ.comp (IsScalarTower.toAlgHom ℂ R S) = ψ)
    (hzero : ∀ δ : S →ₗ[ℂ] ℂ,
      (∀ a b, δ (a*b) = χ a * δ b + χ b * δ a) →
      (∀ b : R, δ (algebraMap R S b) = 0) → δ = 0) :
    Algebra.QuasiFiniteAt R (RingHom.ker χ.toRingHom) := by
  let : Algebra.IsUnramifiedAt R (RingHom.ker χ.toRingHom) :=
    isUnramifiedAt_of_point_derivations χ ψ hcompat hzero
  infer_instance

#print axioms isUnramifiedAt_of_point_derivations
#print axioms quasiFiniteAt_of_point_derivations
#assert_trust kernel isUnramifiedAt_of_point_derivations
#assert_trust kernel quasiFiniteAt_of_point_derivations
end NLA.Proofs.TR06.GraphQuasiFinite
