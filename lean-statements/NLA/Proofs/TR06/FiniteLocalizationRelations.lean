import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Analysis.Complex.Basic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Set

namespace NLA.Proofs.TR06

/-- Evaluation of an actual away-localized element by its actual numerator and
denominator. The representation is supplied by localization, not a new oracle. -/
def awayCoefficientValue {R : Type*} [CommRing R] (t : R)
    (c : Localization.Away t) (ψ : R →+* ℂ) : ℂ :=
  ψ (IsLocalization.Away.sec t c).1 /
    ψ t ^ (IsLocalization.Away.sec t c).2

theorem away_lift_eq_coefficientValue {R : Type*} [CommRing R] (t : R)
    (c : Localization.Away t) (ψ : R →+* ℂ) (hψ : ψ t ≠ 0) :
    (IsLocalization.Away.lift t (isUnit_iff_ne_zero.mpr hψ) :
      Localization.Away t →+* ℂ) c = awayCoefficientValue t c ψ := by
  have hs := congrArg
    (IsLocalization.Away.lift t (isUnit_iff_ne_zero.mpr hψ) :
      Localization.Away t →+* ℂ) (IsLocalization.Away.sec_spec t c)
  simp only [map_mul, IsLocalization.Away.lift_eq, map_pow] at hs
  exact (eq_div_iff (pow_ne_zero _ hψ)).mpr hs

/-- The rational coefficient function is continuous throughout the actual
nonvanishing denominator set, for any continuously evaluated base ring. -/
theorem continuousOn_awayCoefficientValue {R Y : Type*} [CommRing R]
    [TopologicalSpace Y] (t : R) (c : Localization.Away t)
    (ψ : Y → R →+* ℂ) (U : Set Y)
    (hψ : ∀ a, ContinuousOn (fun y => ψ y a) U)
    (ht : ∀ y ∈ U, ψ y t ≠ 0) :
    ContinuousOn (fun y => awayCoefficientValue t c (ψ y)) U := by
  apply (hψ (IsLocalization.Away.sec t c).1).div
    ((hψ t).pow (IsLocalization.Away.sec t c).2)
  intro y hy
  exact pow_ne_zero _ (ht y hy)

/-- Finite localization supplies genuine monic relations for every specified
source coordinate, using the canonical localized scalar action. -/
theorem finite_localization_monic_relations {R S ι : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (t : R)
    [Module.Finite (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t)))]
    (x : ι → S) :
    ∃ P : ι → Polynomial (Localization.Away t), ∀ i,
      (P i).Monic ∧ Polynomial.eval₂
        (algebraMap (Localization.Away t)
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))))
        (algebraMap S
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))) (x i))
        (P i) = 0 := by
  classical
  have H (i : ι) : ∃ p : Polynomial (Localization.Away t), p.Monic ∧
      Polynomial.eval₂
        (algebraMap (Localization.Away t)
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))))
        (algebraMap S
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))) (x i)) p = 0 := by
    exact IsIntegral.of_finite (Localization.Away t) _
  choose P hP hroot using H
  exact ⟨P, fun i => ⟨hP i, hroot i⟩⟩

#print axioms away_lift_eq_coefficientValue
#print axioms continuousOn_awayCoefficientValue
#print axioms finite_localization_monic_relations
#assert_trust kernel away_lift_eq_coefficientValue
#assert_trust kernel continuousOn_awayCoefficientValue
#assert_trust kernel finite_localization_monic_relations

end NLA.Proofs.TR06
