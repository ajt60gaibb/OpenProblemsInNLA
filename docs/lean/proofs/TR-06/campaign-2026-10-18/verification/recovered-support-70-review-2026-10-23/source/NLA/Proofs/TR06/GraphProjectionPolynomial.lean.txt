/-
Copyright (c) 2026. Released under Apache 2.0 license.
Real polynomial jets of genuine complex point derivations.
-/
import Mathlib
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.GraphProjection

variable {S : Type*} [CommRing S] [Algebra ℂ S]

lemma point_derivation_one (χ : S →ₐ[ℂ] ℂ) (δ : S →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = χ a * δ b + χ b * δ a) : δ 1 = 0 := by
  have h := hmul 1 1
  simp only [mul_one,map_one,one_mul] at h
  exact (add_left_cancel (show δ 1 + δ 1 = δ 1 + 0 by simpa using h.symm))

lemma point_derivation_constant (χ : S →ₐ[ℂ] ℂ) (δ : S →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = χ a * δ b + χ b * δ a) (c : ℂ) :
    δ (algebraMap ℂ S c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one,map_smul,point_derivation_one χ δ hmul,smul_zero]

lemma realLinearMap_ofReal_mul (L : ℂ →ₗ[ℝ] ℝ) (c : ℝ) (a : ℂ) :
    L ((c : ℂ)*a) = c*L a := by
  simpa only [Complex.real_smul,smul_eq_mul] using L.map_smul c a

/-- Real-coefficient polynomial evaluation has its literal real value under
an actual character agreeing with the prescribed real coordinate values. -/
theorem character_real_polynomial {ι : Type*} (φ : MvPolynomial ι ℂ →ₐ[ℂ] S)
    (χ : S →ₐ[ℂ] ℂ) (x : ι → ℝ)
    (hχ : ∀ c, χ (φ (MvPolynomial.X c)) = (x c : ℂ)) (P : MvPolynomial ι ℝ) :
    χ (φ (MvPolynomial.map Complex.ofRealHom P)) =
      (MvPolynomial.eval x P : ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ,Complex.ofReal_add]
  | mul_X P c hP => simp only [map_mul,MvPolynomial.map_X,
      MvPolynomial.eval_X,hP,hχ,Complex.ofReal_mul]

/-- Every real linear component of a genuine complex point derivation on real
polynomials is the actual real affine-line derivative. This also applies to
Re and Im separately; no real-to-complex rank assertion is used. -/
theorem hasDerivAt_real_polynomial_of_point_derivation {ι : Type*}
    (φ : MvPolynomial ι ℂ →ₐ[ℂ] S) (χ : S →ₐ[ℂ] ℂ)
    (δ : S →ₗ[ℂ] ℂ) (hmul : ∀ a b, δ (a*b) = χ a * δ b + χ b * δ a)
    (L : ℂ →ₗ[ℝ] ℝ) (x : ι → ℝ)
    (hχ : ∀ c, χ (φ (MvPolynomial.X c)) = (x c : ℂ))
    (P : MvPolynomial ι ℝ) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval
      (fun c => x c + t * L (δ (φ (MvPolynomial.X c)))) P)
      (L (δ (φ (MvPolynomial.map Complex.ofRealHom P)))) 0 := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.map_C,AlgHom.commutes,MvPolynomial.eval_C,
      show ∀ c : ℂ, φ (MvPolynomial.C c) = algebraMap ℂ S c from fun c => φ.commutes c,
      point_derivation_constant χ δ hmul,map_zero] using (hasDerivAt_const (0 : ℝ) c)
  | add P Q hP hQ =>
    convert! hP.add hQ using 1 <;> try rfl
    · ext t; simp only [MvPolynomial.eval_add,Pi.add_apply]
    · simp only [map_add]
  | mul_X P c hP =>
    have hc : HasDerivAt (fun t : ℝ => x c + t * L (δ (φ (MvPolynomial.X c))))
        (L (δ (φ (MvPolynomial.X c)))) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (L (δ (φ (MvPolynomial.X c))))).const_add (x c)
    convert! hP.mul hc using 1
    · ext t; simp only [MvPolynomial.eval_mul,MvPolynomial.eval_X,Pi.mul_apply]
    · simp only [map_mul,MvPolynomial.map_X,hmul,map_add,
        character_real_polynomial φ χ x hχ,hχ,realLinearMap_ofReal_mul,
        zero_mul,add_zero]
      ring

/-- Actual polynomial point derivations are determined by their generator values. -/
theorem point_derivation_polynomial_zero_of_variables {ι : Type*}
    (φ : MvPolynomial ι ℂ →ₐ[ℂ] S) (χ : S →ₐ[ℂ] ℂ)
    (δ : S →ₗ[ℂ] ℂ) (hmul : ∀ a b, δ (a*b) = χ a * δ b + χ b * δ a)
    (hX : ∀ c, δ (φ (MvPolynomial.X c)) = 0) (P : MvPolynomial ι ℂ) :
    δ (φ P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    change δ (φ (algebraMap ℂ (MvPolynomial ι ℂ) c)) = 0
    rw [φ.commutes c]
    exact point_derivation_constant χ δ hmul c
  | add P Q hP hQ => simp only [map_add,hP,hQ,add_zero]
  | mul_X P c hP => simp only [map_mul,hmul,hP,hX,mul_zero,add_zero]

#print axioms point_derivation_polynomial_zero_of_variables
#assert_trust kernel point_derivation_polynomial_zero_of_variables
#print axioms hasDerivAt_real_polynomial_of_point_derivation
#assert_trust kernel character_real_polynomial
#assert_trust kernel hasDerivAt_real_polynomial_of_point_derivation
end NLA.Proofs.TR06.GraphProjection
