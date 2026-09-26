/-
Proposed generic finite-localization statement, before implementation or approval.
No theorem asserting this proposition is declared here.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology.
-/
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Algebraic.Basic
import LeanCert.Tactic.Verification

set_option autoImplicit false
noncomputable section
open Function
universe u v

namespace NLA.TR06.Proposed

/-- A dominant finite-type map of affine integral schemes that is quasi-finite
at the source generic point becomes finite after a nonzero target localization.
The displayed source localization inverts the image of the powers of r; its
canonical scalar action is that of R[1/r], not that of R alone. -/
def GenericFiniteLocalizationStatement : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S],
    Injective (algebraMap R S) →
    Algebra.QuasiFiniteAt R (⊥ : Ideal S) →
    ∃ r : R, r ≠ 0 ∧
      Module.Finite (Localization.Away r)
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers r)))

#check GenericFiniteLocalizationStatement
#print axioms GenericFiniteLocalizationStatement

end NLA.TR06.Proposed
