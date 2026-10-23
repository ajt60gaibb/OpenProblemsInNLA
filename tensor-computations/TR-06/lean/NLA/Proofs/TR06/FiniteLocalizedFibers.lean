import NLA.Proofs.TR06.LocalizedCharacterRelations
import NLA.TR06.AlgebraFiber
import NLA.TR06.FiniteCharacterFiberDefinitions

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Set

namespace NLA.Proofs.TR06
open NLA.TR06 NLA.TR06.Proposed

/-- Finite module generation bounds algebra characters without a freeness
assumption on that module. -/
theorem finite_algHom_of_finite_module (R S K : Type*)
    [CommRing R] [CommRing S] [Field K] [Algebra R S] [Algebra R K]
    [Module.Finite R S] : Finite (S →ₐ[R] K) := by
  classical
  obtain ⟨N, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := S)
  have hind := linearIndependent_algHom_toLinearMap R S K
  have hmap := hind.map' (generatorEvaluation (R := R) (K := K) g)
    (LinearMap.ker_eq_bot.mpr (generatorEvaluation_injective (R := R) (K := K) g hg))
  exact hmap.finite

/-- Every actual character fiber over a nonvanishing finite-localization
denominator is finite. The canonical localized base action is preserved. -/
theorem finite_character_fiber_of_finite_localization {R S : Type*}
    [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S]
    [IsScalarTower ℂ R S] (t : R)
    [Module.Finite (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t)))]
    (χ : R →ₐ[ℂ] ℂ) (ht : χ t ≠ 0) :
    (characterFiber (S := S) χ).Finite := by
  classical
  let Rr := Localization.Away t
  let Sr := Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))
  let α : Rr →+* ℂ := IsLocalization.Away.lift (g := χ.toRingHom) t
    (isUnit_iff_ne_zero.mpr ht)
  let : Algebra Rr ℂ := α.toAlgebra
  have hrestrict (f : characterFiber (S := S) χ) :
      f.val.toRingHom.comp (algebraMap R S) = χ.toRingHom := by
    ext a
    exact DFunLike.congr_fun f.property a
  have hfden (f : characterFiber (S := S) χ) :
      f.val.toRingHom (algebraMap R S t) ≠ 0 := by
    have h := DFunLike.congr_fun f.property t
    exact h.symm ▸ ht
  let F : characterFiber (S := S) χ → (Sr →ₐ[Rr] ℂ) := fun f =>
    { localizedSourceCharacter t f.val.toRingHom (hfden f) with
      commutes' := fun a => by
        change localizedSourceCharacter t f.val.toRingHom (hfden f)
          (algebraMap Rr Sr a) = α a
        have h := DFunLike.congr_fun
          (localizedSourceCharacter_comp_base t f.val.toRingHom (hfden f)) a
        simpa only [RingHom.comp_apply, hrestrict f] using h }
  have hFinj : Function.Injective F := by
    intro f g hfg
    apply Subtype.ext
    ext s
    have h := DFunLike.congr_fun hfg (algebraMap S Sr s)
    change localizedSourceCharacter t f.val.toRingHom (hfden f) (algebraMap S Sr s) =
      localizedSourceCharacter t g.val.toRingHom (hfden g) (algebraMap S Sr s) at h
    calc
      f.val s = localizedSourceCharacter t f.val.toRingHom (hfden f) (algebraMap S Sr s) :=
        (localizedSourceCharacter_algebraMap t f.val.toRingHom (hfden f) s).symm
      _ = localizedSourceCharacter t g.val.toRingHom (hfden g) (algebraMap S Sr s) := h
      _ = g.val s := localizedSourceCharacter_algebraMap t g.val.toRingHom (hfden g) s
  let : Finite (Sr →ₐ[Rr] ℂ) := finite_algHom_of_finite_module Rr Sr ℂ
  let : Finite (characterFiber (S := S) χ) := Finite.of_injective F hFinj
  exact Set.toFinite _

#print axioms finite_algHom_of_finite_module
#print axioms finite_character_fiber_of_finite_localization
#assert_trust kernel finite_algHom_of_finite_module
#assert_trust kernel finite_character_fiber_of_finite_localization

end NLA.Proofs.TR06
