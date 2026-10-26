import NLA.TR06.AdditionLocalization
import NLA.Proofs.TR06.FiniteLocalizationRelations

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set

namespace NLA.Proofs.TR06
open NLA.TR06.Proposed

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- An actual ambient polynomial representing an element of the addition image
algebra. Its pullback is required to equal that element exactly. -/
def additionRepresentative (a : AdditionImage d n r) :
    MvPolynomial (NLA.TR06.TensorIndex d n) ℂ :=
  Classical.choose a.property

theorem additionRepresentative_spec (a : AdditionImage d n r) :
    additionAlgebraHom d n r (additionRepresentative a) = a.val :=
  Classical.choose_spec a.property

/-- Total ambient evaluation, including points outside the addition image. -/
def additionBaseValue (a : AdditionImage d n r) (A : NLA.TR06.Tensor ℂ d n) : ℂ :=
  MvPolynomial.eval (fun q => A q) (additionRepresentative a)

theorem continuous_additionBaseValue (a : AdditionImage d n r) :
    Continuous (additionBaseValue a) := by
  exact (MvPolynomial.continuous_eval _).comp (PiLp.continuous_ofLp 2 _)

/-- On every actual complete character tuple, the total ambient evaluation is
the genuine algebra evaluation. All zero summands are retained. -/
theorem additionBaseValue_characterTuple (a : AdditionImage d n r)
    (f : SegreSource d n r →ₐ[ℂ] ℂ) :
    additionBaseValue a (∑ i, characterTuple f i) = f a.val := by
  have h := DFunLike.congr_fun (character_comp_addition f) (additionRepresentative a)
  simpa only [additionBaseValue, AlgHom.comp_apply, additionRepresentative_spec, MvPolynomial.aeval_eq_eval]
    using h.symm

/-- Total rational ambient coefficients for elements of the actual localized
addition-image algebra. Continuity is only asserted off its denominator. -/
def additionAwayValue (t : AdditionImage d n r) (c : Localization.Away t)
    (A : NLA.TR06.Tensor ℂ d n) : ℂ :=
  additionBaseValue (IsLocalization.Away.sec t c).1 A /
    additionBaseValue t A ^ (IsLocalization.Away.sec t c).2

theorem continuousOn_additionAwayValue (t : AdditionImage d n r)
    (c : Localization.Away t) :
    ContinuousOn (additionAwayValue t c) {A | additionBaseValue t A ≠ 0} := by
  apply (continuous_additionBaseValue (IsLocalization.Away.sec t c).1).continuousOn.div
    ((continuous_additionBaseValue t).continuousOn.pow (IsLocalization.Away.sec t c).2)
  intro A hA
  exact pow_ne_zero _ hA

theorem additionAwayValue_characterTuple (t : AdditionImage d n r)
    (c : Localization.Away t) (f : SegreSource d n r →ₐ[ℂ] ℂ) :
    additionAwayValue t c (∑ i, characterTuple f i) =
      awayCoefficientValue t c (f.toRingHom.comp (additionAlgebraHom d n r).range.val.toRingHom) := by
  simp only [additionAwayValue, awayCoefficientValue, additionBaseValue_characterTuple,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.val_apply]

/-- Actual finite addition localization yields actual monic equations for every
ordered tensor coordinate, before any analytic compactness conclusion. -/
theorem addition_coordinate_monic_relations (t : AdditionImage d n r)
    [Module.Finite (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t)))] :
    ∃ P : (Fin r × NLA.TR06.TensorIndex d n) → Polynomial (Localization.Away t), ∀ iq,
      (P iq).Monic ∧ Polynomial.eval₂
        (algebraMap (Localization.Away t)
          (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t))))
        (algebraMap (SegreSource d n r)
          (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t)))
          (segreCoordinate iq)) (P iq) = 0 :=
  finite_localization_monic_relations t segreCoordinate

#print axioms additionRepresentative_spec
#print axioms continuous_additionBaseValue
#print axioms additionBaseValue_characterTuple
#print axioms continuousOn_additionAwayValue
#print axioms additionAwayValue_characterTuple
#print axioms addition_coordinate_monic_relations
#assert_trust kernel additionRepresentative_spec
#assert_trust kernel continuous_additionBaseValue
#assert_trust kernel additionBaseValue_characterTuple
#assert_trust kernel continuousOn_additionAwayValue
#assert_trust kernel additionAwayValue_characterTuple
#assert_trust kernel addition_coordinate_monic_relations

end NLA.Proofs.TR06
