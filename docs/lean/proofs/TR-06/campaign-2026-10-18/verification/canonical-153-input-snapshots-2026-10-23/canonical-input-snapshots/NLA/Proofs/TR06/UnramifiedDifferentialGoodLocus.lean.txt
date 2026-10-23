/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual unramified addition-coordinate localization gives a genuine injective
pivot-addition derivative, with no Jacobian certificate supplied as data.
-/
import NLA.Proofs.TR06.UnramifiedDifferentialJet
import NLA.TR06.AdditionLocalization
import NLA.TR06.GenericUnramified

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open NLA.TR06 NLA.TR06.Segre NLA.TR06.Proposed
namespace NLA.Proofs.TR06.UnramifiedDifferential

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

def sourceJet (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d)
    (z v : Parameter ℂ q₀) : SegreSource d n r →ₐ[ℂ] TrivSqZeroExt ℂ ℂ :=
  (pivotJet z v).comp (pivotSourceHom q₀ j₀)

def sourceCharacter (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d)
    (z : Parameter ℂ q₀) : SegreSource d n r →ₐ[ℂ] ℂ :=
  (MvPolynomial.aeval (R := ℂ) (fun c => z c)).comp (pivotSourceHom q₀ j₀)

def sourceDirection (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d)
    (z v : Parameter ℂ q₀) : SegreSource d n r →+ ℂ :=
  (TrivSqZeroExt.sndHom ℂ ℂ).toAddMonoidHom.comp
    (sourceJet q₀ j₀ z v).toRingHom.toAddMonoidHom

@[simp] theorem sourceJet_fst (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d)
    (z v : Parameter ℂ q₀) (s : SegreSource d n r) :
    (sourceJet q₀ j₀ z v s).fst = sourceCharacter q₀ j₀ z s :=
  pivotJet_fst z v (pivotSourceHom q₀ j₀ s)

theorem sourceDirection_leibniz (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d)
    (z v : Parameter ℂ q₀) (a b : SegreSource d n r) :
    sourceDirection q₀ j₀ z v (a*b) =
      sourceCharacter q₀ j₀ z a * sourceDirection q₀ j₀ z v b +
      sourceCharacter q₀ j₀ z b * sourceDirection q₀ j₀ z v a := by
  change (sourceJet q₀ j₀ z v (a*b)).snd = _
  rw [map_mul]
  change (sourceJet q₀ j₀ z v a).fst * (sourceJet q₀ j₀ z v b).snd +
    (sourceJet q₀ j₀ z v a).snd * (sourceJet q₀ j₀ z v b).fst = _
  rw [sourceJet_fst, sourceJet_fst]
  change _ = sourceCharacter q₀ j₀ z a * (sourceJet q₀ j₀ z v b).snd +
    sourceCharacter q₀ j₀ z b * (sourceJet q₀ j₀ z v a).snd
  ring

/-- Character evaluation of every ambient polynomial is literally evaluation
at the actual tensor sum, on the entire addition-image base algebra. -/
theorem sourceCharacter_addition_polynomial (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d)
    (z : Parameter ℂ q₀) (p : MvPolynomial (TensorIndex d n) ℂ) :
    sourceCharacter q₀ j₀ z (additionAlgebraHom d n r p) =
      MvPolynomial.eval (fun q => sum q₀ z q) p := by
  have h : (sourceCharacter q₀ j₀ z).comp (additionAlgebraHom d n r) =
      MvPolynomial.aeval (R := ℂ) (fun q => sum q₀ z q) := by
    apply MvPolynomial.algHom_ext
    intro q
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
    change (MvPolynomial.aeval (R := ℂ) (fun c => z c))
      (pivotSourceHom q₀ j₀ (additionAlgebraHom d n r (MvPolynomial.X q))) = _
    rw [pivotSourceHom_addition]
    exact eval_sumPolynomial q₀ z q
  exact AlgHom.congr_fun h p

/-- A derivative-kernel vector annihilates the whole actual addition-image
base algebra, proved by polynomial generation rather than an extra assumption. -/
theorem sourceDirection_base_zero_of_coordinate_jets (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d)
    (z v : Parameter ℂ q₀)
    (hsum : ∀ q, (pivotJet z v (sumPolynomial ℂ q₀ q)).snd = 0) :
    ∀ b : AdditionImage d n r,
      sourceDirection q₀ j₀ z v (algebraMap (AdditionImage d n r) (SegreSource d n r) b) = 0 := by
  have H : (sourceJet q₀ j₀ z v).comp (additionAlgebraHom d n r) =
      (TrivSqZeroExt.inlAlgHom ℂ ℂ ℂ).comp
        (MvPolynomial.aeval (R := ℂ) (fun q => sum q₀ z q)) := by
    apply MvPolynomial.algHom_ext
    intro q
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X]
    change pivotJet z v (pivotSourceHom q₀ j₀
      (additionAlgebraHom d n r (MvPolynomial.X q))) = TrivSqZeroExt.inl (sum q₀ z q)
    rw [pivotSourceHom_addition]
    apply TrivSqZeroExt.ext
    · simp only [pivotJet_fst, eval_sumPolynomial, TrivSqZeroExt.fst_inl]
    · exact hsum q
  intro b
  obtain ⟨p, hp⟩ := b.property
  have h := AlgHom.congr_fun H p
  change sourceDirection q₀ j₀ z v b.val = 0
  rw [← hp]
  change (sourceJet q₀ j₀ z v (additionAlgebraHom d n r p)).snd = 0
  rw [show sourceJet q₀ j₀ z v (additionAlgebraHom d n r p) =
      TrivSqZeroExt.inl ((MvPolynomial.aeval (R := ℂ) (fun q => sum q₀ z q)) p) from h]
  rfl

theorem sourceDirection_base_zero (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d)
    (z v : Parameter ℂ q₀) (hv : fderiv ℂ (sum q₀) z v = 0) :
    ∀ b : AdditionImage d n r,
      sourceDirection q₀ j₀ z v (algebraMap (AdditionImage d n r) (SegreSource d n r) b) = 0 :=
  sourceDirection_base_zero_of_coordinate_jets q₀ j₀ z v
    (pivotJet_sum_zero_of_fderiv_eq_zero q₀ z v hv)

/-- Unramifiedness kills the actual direction once the actual coordinate jets
of addition vanish. The analytic derivative-to-jet bridge is proved separately. -/
theorem pivot_direction_zero_of_unramified
    (t : AdditionImage d n r)
    (hunram : Algebra.FormallyUnramified (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t))))
    (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d) (z v : Parameter ℂ q₀)
    (hz : ∀ i, z ⟨i,none⟩ ≠ 0)
    (hden : sourceCharacter q₀ j₀ z t.val ≠ 0)
    (hsum : ∀ q, (pivotJet z v (sumPolynomial ℂ q₀ q)).snd = 0) : v = 0 := by
  have hzero := point_derivation_zero_of_localized_unramified t hunram
    (sourceCharacter q₀ j₀ z).toRingHom hden (sourceDirection q₀ j₀ z v)
    (sourceDirection_leibniz q₀ j₀ z v)
    (sourceDirection_base_zero_of_coordinate_jets q₀ j₀ z v hsum)
  apply pivotJet_direction_zero q₀ z v hz
  intro i q
  have h := hzero (segreCoordinate (i,q))
  change (pivotJet z v (pivotSourceHom q₀ j₀ (segreCoordinate (i,q)))).snd = 0 at h
  simpa only [pivotSourceHom_coordinate] using h

/-- Actual injectivity at every nonzero-amplitude pivot point whose literal
character denominator lies in a genuine unramified localization. -/
theorem fderiv_pivot_sum_injective_of_unramified
    (t : AdditionImage d n r)
    (hunram : Algebra.FormallyUnramified (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t))))
    (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d) (z : Parameter ℂ q₀)
    (hz : ∀ i, z ⟨i,none⟩ ≠ 0)
    (hden : sourceCharacter q₀ j₀ z t.val ≠ 0) :
    Function.Injective (fderiv ℂ (sum q₀) z) := by
  have hker (v : Parameter ℂ q₀) (hv : fderiv ℂ (sum q₀) z v = 0) : v = 0 := by
    exact pivot_direction_zero_of_unramified t hunram q₀ j₀ z v hz hden
      (pivotJet_sum_zero_of_fderiv_eq_zero q₀ z v hv)
  intro x y hxy
  have hzero : fderiv ℂ (sum q₀) z (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hker (x-y) hzero)

/-- Actual original genericity supplies a genuine nonzero unramified base
localization, before any analytic or geometric conclusion is extracted. -/
theorem exists_unramified_addition_denominator (hd : 0 < d)
    (hgeneric : GenericComplexIdentifiable d n r) :
    ∃ t : AdditionImage d n r, t ≠ 0 ∧
      Algebra.FormallyUnramified (Localization.Away t)
        (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t))) := by
  let S := SegreSource d n r
  let R := AdditionImage d n r
  let : Algebra.FiniteType ℂ S := (segre_algebra_structure d n r).2
  let : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R S
  obtain ⟨p, ⟨A,hA,hp⟩, hident⟩ := hgeneric
  have hqf := (addition_finite_localization d n r hd ⟨A,hA,hident A hA hp⟩).1
  obtain ⟨t,ht,hu⟩ := generic_unramified_localization R S Subtype.val_injective hqf
  exact ⟨t,ht,hu⟩

/-- The original nonvacuous generic complex identifiability supplies an actual
nonzero denominator with injective pivot-addition derivatives on its good set. -/
theorem exists_unramified_derivative_denominator (hd : 0 < d)
    (hgeneric : GenericComplexIdentifiable d n r) :
    ∃ t : AdditionImage d n r, t ≠ 0 ∧
      ∀ (q₀ : Fin r → TensorIndex d n) (j₀ : Fin d) (z : Parameter ℂ q₀),
        (∀ i, z ⟨i,none⟩ ≠ 0) → sourceCharacter q₀ j₀ z t.val ≠ 0 →
        Function.Injective (fderiv ℂ (sum q₀) z) := by
  obtain ⟨t,ht,hu⟩ := exists_unramified_addition_denominator hd hgeneric
  refine ⟨t,ht,?_⟩
  intro q₀ j₀ z hz hden
  exact fderiv_pivot_sum_injective_of_unramified t hu q₀ j₀ z hz hden

#print axioms sourceCharacter_addition_polynomial
#print axioms sourceDirection_base_zero_of_coordinate_jets
#print axioms pivot_direction_zero_of_unramified
#print axioms exists_unramified_addition_denominator
#print axioms sourceDirection_base_zero
#print axioms fderiv_pivot_sum_injective_of_unramified
#print axioms exists_unramified_derivative_denominator
#assert_trust kernel sourceCharacter_addition_polynomial
#assert_trust kernel sourceDirection_base_zero_of_coordinate_jets
#assert_trust kernel pivot_direction_zero_of_unramified
#assert_trust kernel exists_unramified_addition_denominator
#assert_trust kernel sourceDirection_base_zero
#assert_trust kernel fderiv_pivot_sum_injective_of_unramified
#assert_trust kernel exists_unramified_derivative_denominator
end NLA.Proofs.TR06.UnramifiedDifferential
