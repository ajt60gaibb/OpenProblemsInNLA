/-
Copyright (c) 2026. Released under Apache 2.0 license.
The actual square-zero uniqueness argument for a localized point derivation.
-/
import Mathlib
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Function
namespace NLA.Proofs.TR06.UnramifiedDifferential

/-- A point derivation vanishing on the base vanishes at an unramified point.
The denominator is required to have a genuinely nonzero value at the character;
no Jacobian certificate or differential injectivity is assumed. -/
theorem point_derivation_zero_of_unramified_away
    {R S Sr : Type*} [CommRing R] [CommRing S] [CommRing Sr]
    [Algebra R S] [Algebra R Sr] [Algebra S Sr] [IsScalarTower R S Sr]
    (r : R) [IsLocalization.Away (algebraMap R S r) Sr]
    [Algebra.FormallyUnramified R Sr]
    (χ : S →+* ℂ) (hden : χ (algebraMap R S r) ≠ 0)
    (δ : S →+ ℂ)
    (hmul : ∀ a b, δ (a*b) = χ a * δ b + χ b * δ a)
    (hbase : ∀ b : R, δ (algebraMap R S b) = 0) :
    ∀ s : S, δ s = 0 := by
  let χR : R →+* ℂ := χ.comp (algebraMap R S)
  let : Algebra R ℂ := χR.toAlgebra
  let f : S →ₐ[R] TrivSqZeroExt ℂ ℂ :=
    { toFun := fun s => ⟨χ s, δ s⟩
      map_zero' := by ext <;> simp
      map_one' := by
        ext
        · exact χ.map_one
        · simpa using hbase (1 : R)
      map_add' := by
        intro a b
        apply TrivSqZeroExt.ext
        · change χ (a+b) = χ a + χ b; exact χ.map_add a b
        · change δ (a+b) = δ a + δ b; exact δ.map_add a b
      map_mul' := by
        intro a b
        ext
        · exact χ.map_mul a b
        · change δ (a*b) = χ a * δ b + δ a * χ b
          rw [hmul, mul_comm (δ a) (χ b)]
      commutes' := by
        intro b
        ext
        · rfl
        · exact hbase b }
  let χA : S →ₐ[R] ℂ := { χ with commutes' := fun _ => rfl }
  let f0 : S →ₐ[R] TrivSqZeroExt ℂ ℂ := (TrivSqZeroExt.inlAlgHom R ℂ ℂ).comp χA
  have hf : IsUnit (f (algebraMap R S r)) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact isUnit_iff_ne_zero.mpr hden
  have hf0 : IsUnit (f0 (algebraMap R S r)) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact isUnit_iff_ne_zero.mpr hden
  let F : Sr →ₐ[R] TrivSqZeroExt ℂ ℂ := IsLocalization.Away.liftAlgHom (algebraMap R S r) hf
  let F0 : Sr →ₐ[R] TrivSqZeroExt ℂ ℂ := IsLocalization.Away.liftAlgHom (algebraMap R S r) hf0
  have hF (s : S) : F (algebraMap S Sr s) = f s :=
    IsLocalization.Away.lift_eq (algebraMap R S r) hf s
  have hF0 (s : S) : F0 (algebraMap S Sr s) = f0 s :=
    IsLocalization.Away.lift_eq (algebraMap R S r) hf0 s
  have hcomp : (TrivSqZeroExt.fstHom R ℂ ℂ).comp F =
      (TrivSqZeroExt.fstHom R ℂ ℂ).comp F0 := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R S r))
    ext s
    change (F (algebraMap S Sr s)).fst = (F0 (algebraMap S Sr s)).fst
    rw [hF, hF0]
    rfl
  have heq : F = F0 := Algebra.FormallyUnramified.lift_unique_of_ringHom
    (TrivSqZeroExt.fstHom R ℂ ℂ).toRingHom
    ⟨2, TrivSqZeroExt.kerIdeal_sq ℂ ℂ⟩ F F0
    (by exact congrArg AlgHom.toRingHom hcomp)
  intro s
  have hs := congrArg (fun g : Sr →ₐ[R] TrivSqZeroExt ℂ ℂ => (g (algebraMap S Sr s)).snd) heq
  rw [hF, hF0] at hs
  exact hs

/-- The preceding result for the canonical simultaneously localized source
and base used by the retained generic-unramified theorem. -/
theorem point_derivation_zero_of_localized_unramified
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R)
    (hunram : Algebra.FormallyUnramified (Localization.Away r)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers r))))
    (χ : S →+* ℂ) (hden : χ (algebraMap R S r) ≠ 0)
    (δ : S →+ ℂ)
    (hmul : ∀ a b, δ (a*b) = χ a * δ b + χ b * δ a)
    (hbase : ∀ b : R, δ (algebraMap R S b) = 0) :
    ∀ s : S, δ s = 0 := by
  let Sr := Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers r))
  let : IsLocalization.Away (algebraMap R S r) Sr := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers r)) Sr)
  let : Algebra.FormallyUnramified (Localization.Away r) Sr := hunram
  let : Algebra.FormallyUnramified R (Localization.Away r) :=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers r)
  let : Algebra.FormallyUnramified R Sr :=
    Algebra.FormallyUnramified.comp R (Localization.Away r) Sr
  exact point_derivation_zero_of_unramified_away (Sr := Sr) r χ hden δ hmul hbase

#print axioms point_derivation_zero_of_unramified_away
#print axioms point_derivation_zero_of_localized_unramified
#assert_trust kernel point_derivation_zero_of_unramified_away
#assert_trust kernel point_derivation_zero_of_localized_unramified
end NLA.Proofs.TR06.UnramifiedDifferential
