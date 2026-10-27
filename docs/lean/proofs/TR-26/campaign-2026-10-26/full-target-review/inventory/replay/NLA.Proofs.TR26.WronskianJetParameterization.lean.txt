import NLA.Proofs.TR26.WronskianJets
import NLA.Proofs.TR26.Numerator
import Mathlib.Algebra.Polynomial.OfFn

/-! Explicit Taylor coordinates for every numerator in the nonisotropic
double-Wronskian incidence. The free tail is finite dimensional. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem polynomial_secondJet_expansion (N : Polynomial ℂ) (r : ℂ) :
    ∃ tail : Polynomial ℂ, tail.natDegree ≤ N.natDegree - 3 ∧
      N = secondJetPolynomial r (N.eval r) (N.derivative.eval r)
        ((Polynomial.taylor r N).coeff 2) tail := by
  let P := Polynomial.taylor r N
  have h0 := Polynomial.X_mul_divX_add P
  have h1 := Polynomial.X_mul_divX_add P.divX
  have h2 := Polynomial.X_mul_divX_add P.divX.divX
  simp only [Polynomial.coeff_divX] at h1 h2
  have hsum : P = C (P.coeff 0) + C (P.coeff 1) * X +
      C (P.coeff 2) * X ^ 2 + X ^ 3 * P.divX.divX.divX := by
    linear_combination -h0 - X * h1 - X ^ 2 * h2
  refine ⟨Polynomial.taylor (-r) P.divX.divX.divX, ?_, ?_⟩
  · simp only [Polynomial.natDegree_taylor,
      Polynomial.natDegree_divX_eq_natDegree_tsub_one, P]
    omega
  · have h := congrArg (Polynomial.taylor (-r)) hsum
    have hX : (X : Polynomial ℂ) + C (-r) = X - C r := by simp [sub_eq_add_neg]
    simpa only [map_add, Polynomial.taylor_mul, Polynomial.taylor_pow,
      Polynomial.taylor_C, Polynomial.taylor_X, hX,
      P, Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero,
      Polynomial.taylor_coeff_zero, Polynomial.taylor_coeff_one,
      secondJetPolynomial] using h

theorem double_Wronskian_root_iff_parameterization (N D : Polynomial ℂ) (r : ℂ)
    (hD : D.eval r ≠ 0) :
    ((polynomialWronskian N D).eval r = 0 ∧
      (polynomialWronskian N D).derivative.eval r = 0) ↔
    ∃ a0 : ℂ, ∃ tail : Polynomial ℂ, tail.natDegree ≤ N.natDegree - 3 ∧
      N = secondJetPolynomial r a0 (a0 * D.derivative.eval r / D.eval r)
        (a0 * D.derivative.derivative.eval r / (2 * D.eval r)) tail := by
  constructor
  · intro hroot
    obtain ⟨tail, htail, hN⟩ := polynomial_secondJet_expansion N r
    have hjet := (secondJetPolynomial_double_root_iff D r (N.eval r)
      (N.derivative.eval r) ((Polynomial.taylor r N).coeff 2) tail hD).mp
      (by simpa only [← hN] using hroot)
    refine ⟨N.eval r, tail, htail, ?_⟩
    rw [← hjet.1, ← hjet.2]
    exact hN
  · rintro ⟨a0, tail, _, rfl⟩
    exact (secondJetPolynomial_double_root_iff D r a0 _ _ tail hD).mpr ⟨rfl, rfl⟩

def nonisotropicJetNumerator (d : ℕ) (r a0 : ℂ) (tail : Fin (2 * d - 2) → ℂ) :
    Polynomial ℂ :=
  secondJetPolynomial r a0
    (a0 * (affineDenominator d).derivative.eval r / (affineDenominator d).eval r)
    (a0 * (affineDenominator d).derivative.derivative.eval r /
      (2 * (affineDenominator d).eval r))
    (Polynomial.ofFn (2 * d - 2) tail)

theorem secondJetPolynomial_natDegree_le {m : ℕ} (hm : 3 ≤ m)
    (r a0 a1 a2 : ℂ) (tail : Polynomial ℂ) (htail : tail.natDegree ≤ m - 3) :
    (secondJetPolynomial r a0 a1 a2 tail).natDegree ≤ m := by
  have h1 : (C a1 * (X - C r) : Polynomial ℂ).natDegree ≤ m := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp; omega)
  have h2 : (C a2 * (X - C r) ^ 2 : Polynomial ℂ).natDegree ≤ m := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp; omega)
  have h3 : ((X - C r) ^ 3 * tail).natDegree ≤ m := by
    have h : ((X - C r) ^ 3 * tail).natDegree ≤
        ((X - C r) ^ 3).natDegree + tail.natDegree := Polynomial.natDegree_mul_le
    simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at h
    omega
  exact Polynomial.natDegree_add_le_of_degree_le
    (Polynomial.natDegree_add_le_of_degree_le
      (Polynomial.natDegree_add_le_of_degree_le (by simp) h1) h2) h3

theorem nonisotropicJetNumerator_natDegree_le {d : ℕ} (hd : 2 ≤ d)
    (r a0 : ℂ) (tail : Fin (2 * d - 2) → ℂ) :
    (nonisotropicJetNumerator d r a0 tail).natDegree ≤ 2 * d := by
  apply secondJetPolynomial_natDegree_le (by omega)
  have h := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ 2 * d - 2) tail
  omega

theorem exists_parameter_nonisotropicJetNumerator {d : ℕ} (hd : 2 ≤ d)
    (r a0 : ℂ) (tail : Fin (2 * d - 2) → ℂ) :
    ∃ H : Parameter d, affineNumerator H = nonisotropicJetNumerator d r a0 tail :=
  affineNumerator_surjective_degreeLE d _ (nonisotropicJetNumerator_natDegree_le hd r a0 tail)

theorem affine_double_Wronskian_root_iff_finite_parameterization {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) (r : ℂ) (hD : (affineDenominator d).eval r ≠ 0) :
    ((affineWronskian H).eval r = 0 ∧ (affineWronskian H).derivative.eval r = 0) ↔
    ∃ a0 : ℂ, ∃ tail : Fin (2 * d - 2) → ℂ,
      affineNumerator H = nonisotropicJetNumerator d r a0 tail := by
  change ((polynomialWronskian (affineNumerator H) (affineDenominator d)).eval r = 0 ∧
    (polynomialWronskian (affineNumerator H) (affineDenominator d)).derivative.eval r = 0) ↔ _
  constructor
  · intro hroot
    obtain ⟨a0, tail, htail, hN⟩ :=
      (double_Wronskian_root_iff_parameterization _ _ _ hD).mp hroot
    have hdeg := affineNumerator_natDegree_le H
    have hlt : tail.natDegree < 2 * d - 2 := by omega
    refine ⟨a0, Polynomial.toFn (2 * d - 2) tail, ?_⟩
    simpa only [nonisotropicJetNumerator,
      Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hlt] using hN
  · rintro ⟨a0, tail, hN⟩
    rw [hN]
    exact (secondJetPolynomial_double_root_iff _ r a0 _ _
      (Polynomial.ofFn (2 * d - 2) tail) hD).mpr ⟨rfl, rfl⟩

#assert_trust kernel polynomial_secondJet_expansion
#assert_trust kernel double_Wronskian_root_iff_parameterization
#assert_trust kernel secondJetPolynomial_natDegree_le
#assert_trust kernel nonisotropicJetNumerator_natDegree_le
#assert_trust kernel exists_parameter_nonisotropicJetNumerator
#assert_trust kernel affine_double_Wronskian_root_iff_finite_parameterization
#print axioms affine_double_Wronskian_root_iff_finite_parameterization
end NLA.Proofs.TR26
