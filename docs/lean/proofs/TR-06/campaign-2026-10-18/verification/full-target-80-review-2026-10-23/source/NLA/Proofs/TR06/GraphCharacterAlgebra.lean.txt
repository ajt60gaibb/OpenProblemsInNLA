/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual characters of the pivot/radius quotient and its away localization.
-/
import NLA.Proofs.TR06.NormalizedGraphAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR06.GraphCharacter
open NLA.TR06 NLA.TR06.Segre GraphAlgebra
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Actual polynomial evaluation at pivot and radius coordinates. -/
def polynomialCharacter (q₀ : Fin r → TensorIndex d n) (x : Variable q₀ → ℂ) :
    PolynomialRing q₀ →ₐ[ℂ] ℂ := MvPolynomial.aeval x

/-- The actual radius equations make polynomial evaluation descend to the
whole quotient, retaining its other branches and nilpotents. -/
def quotientCharacter (q₀ : Fin r → TensorIndex d n) (x : Variable q₀ → ℂ)
    (hx : ∀ i, polynomialCharacter q₀ x (radiusEquation q₀ i) = 0) :
    QuotientRing q₀ →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (radiusIdeal q₀) (polynomialCharacter q₀ x) (by
    intro P hP
    have hle : radiusIdeal q₀ ≤ RingHom.ker (polynomialCharacter q₀ x).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hx i
    exact hle hP)

@[simp] theorem quotientCharacter_quotientHom (q₀ : Fin r → TensorIndex d n)
    (x : Variable q₀ → ℂ) (hx) (P : PolynomialRing q₀) :
    quotientCharacter q₀ x hx (quotientHom q₀ P) = polynomialCharacter q₀ x P := rfl

/-- The genuine character of the actual source localization. -/
def characterFromValues (q₀ : Fin r → TensorIndex d n) (x : Variable q₀ → ℂ)
    (hx : ∀ i, polynomialCharacter q₀ x (radiusEquation q₀ i) = 0)
    (hr : ∀ i, x (Sum.inr i) ≠ 0) : Source q₀ →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom (denominator q₀) (show IsUnit
      (quotientCharacter q₀ x hx (denominator q₀)) from isUnit_iff_ne_zero.mpr (by
    simp only [denominator, map_prod, quotientCharacter_quotientHom]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by
      simpa only [polynomialCharacter,radius,MvPolynomial.aeval_X] using hr i)))

@[simp] theorem characterFromValues_sourceHom (q₀ : Fin r → TensorIndex d n)
    (x : Variable q₀ → ℂ) (hx) (hr) (P : PolynomialRing q₀) :
    characterFromValues q₀ x hx hr (sourceHom q₀ P) = polynomialCharacter q₀ x P := by
  simp only [characterFromValues, sourceHom, AlgHom.comp_apply,
    IsScalarTower.toAlgHom_apply, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq]
  rfl

@[simp] theorem characterFromValues_radius (q₀ : Fin r → TensorIndex d n)
    (x : Variable q₀ → ℂ) (hx) (hr) (i : Fin r) :
    characterFromValues q₀ x hx hr (sourceRadius q₀ i) = x (Sum.inr i) := by
  simp [sourceRadius,polynomialCharacter,radius]

@[simp] theorem characterFromValues_variable (q₀ : Fin r → TensorIndex d n)
    (x : Variable q₀ → ℂ) (hx) (hr) (c : Variable q₀) :
    characterFromValues q₀ x hx hr (sourceHom q₀ (MvPolynomial.X c)) = x c := by
  simp [polynomialCharacter]

@[simp] theorem characterFromValues_radiusInverse (q₀ : Fin r → TensorIndex d n)
    (x : Variable q₀ → ℂ) (hx) (hr) (i : Fin r) :
    characterFromValues q₀ x hx hr (sourceRadiusInverse q₀ i) = (x (Sum.inr i))⁻¹ := by
  have h := congrArg (characterFromValues q₀ x hx hr) (sourceRadius_mul_inverse q₀ i)
  rw [map_mul,map_one,characterFromValues_radius] at h
  exact eq_inv_of_mul_eq_one_right h

#print axioms characterFromValues
#print axioms characterFromValues_sourceHom
#print axioms characterFromValues_radiusInverse
#assert_trust kernel characterFromValues
#assert_trust kernel characterFromValues_sourceHom
#assert_trust kernel characterFromValues_radiusInverse
end NLA.Proofs.TR06.GraphCharacter
