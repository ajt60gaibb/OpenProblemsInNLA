/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual generator detection of point derivations in the pivot/radius algebra.
-/
import NLA.Proofs.TR06.GraphCharacterReal
import NLA.Proofs.TR06.GraphProjectionPolynomial

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR06.GraphProjection
open NLA.TR06 NLA.TR06.Segre GraphAlgebra GraphCharacter
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Values on the actual pivot/radius polynomial generators detect every
point derivation of the actual quotient localization. -/
theorem point_derivation_zero_of_variables (q₀ : Fin r → TensorIndex d n)
    (χ : Source q₀ →ₐ[ℂ] ℂ) (δ : Source q₀ →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = χ a * δ b + χ b * δ a)
    (hvar : ∀ c : Variable q₀, δ (sourceHom q₀ (MvPolynomial.X c)) = 0) : δ = 0 := by
  have hpoly (P : PolynomialRing q₀) : δ (sourceHom q₀ P) = 0 := by
    induction P using MvPolynomial.induction_on with
    | C c =>
      change δ (sourceHom q₀ (algebraMap ℂ (PolynomialRing q₀) c)) = 0
      rw [(sourceHom q₀).commutes c]
      exact point_derivation_constant χ δ hmul c
    | add P Q hP hQ => simp only [map_add,hP,hQ,add_zero]
    | mul_X P c hP => simp only [map_mul,hmul,hP,hvar,mul_zero,add_zero]
  have hquot (a : QuotientRing q₀) : δ (algebraMap (QuotientRing q₀) (Source q₀) a) = 0 := by
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective a
    change δ (sourceHom q₀ P) = 0
    exact hpoly P
  apply LinearMap.ext
  intro s
  obtain ⟨⟨a,t⟩,ht⟩ := IsLocalization.surj (Submonoid.powers (denominator q₀)) s
  have h := congrArg δ ht
  rw [hmul,hquot,hquot,mul_zero,zero_add] at h
  have hu : χ (algebraMap (QuotientRing q₀) (Source q₀) t) ≠ 0 := by
    exact IsUnit.ne_zero ((IsLocalization.map_units (Source q₀) t).map χ.toRingHom)
  exact (mul_eq_zero.mp h).resolve_left hu

/-- The literal radius relation determines the infinitesimal radius from
actual summand derivatives at the actual positive-radius character. -/
theorem point_derivation_radius_relation (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0) (δ : Source q₀ →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = character q₀ z hz a * δ b + character q₀ z hz b * δ a)
    (i : Fin r) :
    (‖summands q₀ z i‖ : ℂ) * δ (sourceRadius q₀ i) =
      ∑ q, (summands q₀ z i q : ℂ) * δ (sourceSummand q₀ i q) := by
  have h := congrArg δ (sourceRadius_sq q₀ i)
  simp only [pow_two,hmul,map_sum,character_source_radius,character_source_summand] at h
  have hsum : (∑ q, ((summands q₀ z i q : ℂ) * δ (sourceSummand q₀ i q) +
      (summands q₀ z i q : ℂ) * δ (sourceSummand q₀ i q))) =
      2 * ∑ q, (summands q₀ z i q : ℂ) * δ (sourceSummand q₀ i q) := by
    rw [Finset.sum_add_distrib]; ring
  rw [hsum] at h
  linear_combination h / 2

/-- At the actual positive-radius character, pivot directions alone detect
all point derivations: the actual radius equations force the radius directions. -/
theorem point_derivation_zero_of_pivot_variables (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0) (δ : Source q₀ →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = character q₀ z hz a * δ b + character q₀ z hz b * δ a)
    (hX : ∀ c : Coordinate q₀, δ (sourceHom q₀ (MvPolynomial.X (Sum.inl c))) = 0) : δ = 0 := by
  let φ : MvPolynomial (Coordinate q₀) ℂ →ₐ[ℂ] Source q₀ :=
    (sourceHom q₀).comp (MvPolynomial.rename Sum.inl)
  have hpoly (P : MvPolynomial (Coordinate q₀) ℂ) : δ (φ P) = 0 :=
    point_derivation_polynomial_zero_of_variables φ (character q₀ z hz) δ hmul
      (by simpa only [φ,AlgHom.comp_apply,MvPolynomial.rename_X] using hX) P
  have hs (i : Fin r) (q : TensorIndex d n) : δ (sourceSummand q₀ i q) = 0 :=
    hpoly (summandPolynomial ℂ q₀ i q)
  apply point_derivation_zero_of_variables q₀ (character q₀ z hz) δ hmul
  intro c
  cases c with
  | inl c => exact hX c
  | inr i =>
    have h := point_derivation_radius_relation q₀ z hz δ hmul i
    simp only [hs,mul_zero,Finset.sum_const_zero] at h
    have hn : (‖summands q₀ z i‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (summands_ne_zero q₀ z hz i))
    exact (mul_eq_zero.mp h).resolve_left hn

#print axioms point_derivation_zero_of_pivot_variables
#assert_trust kernel point_derivation_zero_of_pivot_variables
#print axioms point_derivation_zero_of_variables
#print axioms point_derivation_radius_relation
#assert_trust kernel point_derivation_zero_of_variables
#assert_trust kernel point_derivation_radius_relation
end NLA.Proofs.TR06.GraphProjection
