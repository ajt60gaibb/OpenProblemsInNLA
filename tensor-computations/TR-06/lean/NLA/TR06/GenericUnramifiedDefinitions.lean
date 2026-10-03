/-
Proposed generic characteristic-zero unramifiedness statements, before proof.
No theorem asserting either proposition is declared here.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology.
-/
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.Algebra.CharP.Algebra
import LeanCert.Tactic.Verification

set_option autoImplicit false
noncomputable section
open Function
universe u v

namespace NLA.TR06.Proposed

/-- A dominant finite-type map of integral domains in characteristic zero that
is quasi-finite at the source generic point is unramified there. -/
def GenericUnramifiedAtStatement : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [CharZero R]
    [Algebra R S] [Algebra.FiniteType R S],
    Injective (algebraMap R S) →
    Algebra.QuasiFiniteAt R (⊥ : Ideal S) →
    Algebra.IsUnramifiedAt R (⊥ : Ideal S)

/-- Under the same hypotheses, one nonzero base denominator makes the entire
localized source formally unramified over the canonically localized base. -/
def GenericUnramifiedLocalizationStatement : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [CharZero R]
    [Algebra R S] [Algebra.FiniteType R S],
    Injective (algebraMap R S) →
    Algebra.QuasiFiniteAt R (⊥ : Ideal S) →
    ∃ r : R, r ≠ 0 ∧
      Algebra.FormallyUnramified (Localization.Away r)
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers r)))

#check GenericUnramifiedAtStatement
#check GenericUnramifiedLocalizationStatement

end NLA.TR06.Proposed
