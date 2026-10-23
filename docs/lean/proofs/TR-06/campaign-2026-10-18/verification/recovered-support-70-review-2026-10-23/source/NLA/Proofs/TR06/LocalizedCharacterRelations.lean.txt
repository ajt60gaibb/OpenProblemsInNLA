import NLA.Proofs.TR06.FiniteLocalizationRelations
import Mathlib.Algebra.Polynomial.Eval.Coeff

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.TR06

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual character extended to the canonical source localization. -/
def localizedSourceCharacter (t : R) (φ : S →+* ℂ)
    (ht : φ (algebraMap R S t) ≠ 0) :
    Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t)) →+* ℂ := by
  letI : IsLocalization.Away (algebraMap R S t)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))) := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))))
  exact IsLocalization.Away.lift (algebraMap R S t) (isUnit_iff_ne_zero.mpr ht)

theorem localizedSourceCharacter_algebraMap (t : R) (φ : S →+* ℂ)
    (ht : φ (algebraMap R S t) ≠ 0) (s : S) :
    localizedSourceCharacter t φ ht
      (algebraMap S (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))) s) = φ s := by
  let : IsLocalization.Away (algebraMap R S t)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))) := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))))
  exact IsLocalization.Away.lift_eq (algebraMap R S t) _ s

/-- The extended source character restricts to the exact extended base
character, for the canonical localized scalar action. -/
theorem localizedSourceCharacter_comp_base (t : R) (φ : S →+* ℂ)
    (ht : φ (algebraMap R S t) ≠ 0) :
    (localizedSourceCharacter t φ ht).comp
        (algebraMap (Localization.Away t)
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t)))) =
      (IsLocalization.Away.lift (g := φ.comp (algebraMap R S)) t (isUnit_iff_ne_zero.mpr ht) :
        Localization.Away t →+* ℂ) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  ext a
  change localizedSourceCharacter t φ ht
    (algebraMap (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t)))
      (algebraMap R (Localization.Away t) a)) = _
  have h : algebraMap (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t)))
      (algebraMap R (Localization.Away t) a) =
      algebraMap S (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t)))
        (algebraMap R S a) := by
    rw [← IsScalarTower.algebraMap_apply R (Localization.Away t),
      ← IsScalarTower.algebraMap_apply R S]
  rw [h, localizedSourceCharacter_algebraMap, RingHom.comp_apply, IsLocalization.Away.lift_eq]
  rfl

/-- Every actual character transports a genuine localized monic relation to
an actual scalar polynomial root. No finiteness or rank conclusion is assumed. -/
theorem localized_relation_isRoot (t : R) (x : S)
    (p : Polynomial (Localization.Away t))
    (hroot : Polynomial.eval₂
      (algebraMap (Localization.Away t)
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))))
      (algebraMap S
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))) x) p = 0)
    (φ : S →+* ℂ) (ht : φ (algebraMap R S t) ≠ 0) :
    (p.map (IsLocalization.Away.lift (g := φ.comp (algebraMap R S)) t (isUnit_iff_ne_zero.mpr ht) :
      Localization.Away t →+* ℂ)).IsRoot (φ x) := by
  have h := congrArg (localizedSourceCharacter t φ ht) hroot
  rw [Polynomial.hom_eval₂, localizedSourceCharacter_comp_base,
    localizedSourceCharacter_algebraMap, map_zero] at h
  simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using h

#print axioms localizedSourceCharacter_algebraMap
#print axioms localizedSourceCharacter_comp_base
#print axioms localized_relation_isRoot
#assert_trust kernel localizedSourceCharacter_algebraMap
#assert_trust kernel localizedSourceCharacter_comp_base
#assert_trust kernel localized_relation_isRoot

end NLA.Proofs.TR06
