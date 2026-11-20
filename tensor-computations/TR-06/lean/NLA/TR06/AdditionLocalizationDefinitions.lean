import NLA.TR06.SegreAlgebra
import NLA.TR06.GenericFiniteLocalization

set_option autoImplicit false
noncomputable section
namespace NLA.TR06.Proposed

/-- Actual coordinate algebra of the closure of the addition image, represented
as the image subalgebra inside the integral source coordinate algebra. -/
abbrev AdditionImage (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :=
  ↥(additionAlgebraHom d n r).range

/-- One actual identifiable exact-rank tensor supplies a finite nonempty source
fiber, hence generic quasi-finiteness and a nonzero base finite localization. -/
def AdditionFiniteLocalizationStatement : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ) (r : ℕ), 0 < d →
    (∃ A : Tensor ℂ d n, ExactRank r A ∧ Identifiable r A) →
    Algebra.QuasiFiniteAt (AdditionImage d n r) (⊥ : Ideal (SegreSource d n r)) ∧
    ∃ t : AdditionImage d n r, t ≠ 0 ∧
      Module.Finite (Localization.Away t)
        (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t)))

#check AdditionFiniteLocalizationStatement
end NLA.TR06.Proposed
