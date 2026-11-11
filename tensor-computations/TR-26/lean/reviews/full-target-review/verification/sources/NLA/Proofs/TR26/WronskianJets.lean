import NLA.Proofs.TR26.WronskianPencilDegree
import Mathlib.Algebra.Polynomial.Taylor

/-! Exact Taylor-jet coordinates for the genuine nonisotropic double-Wronskian
incidence. These are deterministic polynomial identities, not genericity or
reducedness assumptions. The quadratic coordinate is a Taylor coefficient. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.Proofs.TR26

def secondJetPolynomial (r a0 a1 a2 : ℂ) (tail : Polynomial ℂ) : Polynomial ℂ :=
  C a0 + C a1 * (X - C r) + C a2 * (X - C r) ^ 2 + (X - C r) ^ 3 * tail

@[simp] theorem secondJetPolynomial_eval (r a0 a1 a2 : ℂ) (tail : Polynomial ℂ) :
    (secondJetPolynomial r a0 a1 a2 tail).eval r = a0 := by
  simp [secondJetPolynomial]

@[simp] theorem secondJetPolynomial_derivative_eval (r a0 a1 a2 : ℂ) (tail : Polynomial ℂ) :
    (secondJetPolynomial r a0 a1 a2 tail).derivative.eval r = a1 := by
  simp [secondJetPolynomial, Polynomial.derivative_pow]

@[simp] theorem secondJetPolynomial_second_derivative_eval (r a0 a1 a2 : ℂ) (tail : Polynomial ℂ) :
    (secondJetPolynomial r a0 a1 a2 tail).derivative.derivative.eval r = 2 * a2 := by
  simp [secondJetPolynomial, Polynomial.derivative_pow, Polynomial.derivative_mul,
    Polynomial.derivative_add, Polynomial.derivative_sub]
  ring

theorem polynomialWronskian_derivative (N D : Polynomial ℂ) :
    (polynomialWronskian N D).derivative = N.derivative.derivative * D - N * D.derivative.derivative := by
  simp only [polynomialWronskian, Polynomial.derivative_sub, Polynomial.derivative_mul]
  ring

theorem double_Wronskian_root_iff_jets (N D : Polynomial ℂ) (r : ℂ) (hD : D.eval r ≠ 0) :
    ((polynomialWronskian N D).eval r = 0 ∧
      (polynomialWronskian N D).derivative.eval r = 0) ↔
    (N.derivative.eval r = N.eval r * D.derivative.eval r / D.eval r ∧
      N.derivative.derivative.eval r = N.eval r * D.derivative.derivative.eval r / D.eval r) := by
  rw [polynomialWronskian_derivative]
  simp only [polynomialWronskian, Polynomial.eval_sub, Polynomial.eval_mul, sub_eq_zero,
    eq_div_iff hD]

theorem secondJetPolynomial_double_root_iff (D : Polynomial ℂ) (r a0 a1 a2 : ℂ)
    (tail : Polynomial ℂ) (hD : D.eval r ≠ 0) :
    ((polynomialWronskian (secondJetPolynomial r a0 a1 a2 tail) D).eval r = 0 ∧
      (polynomialWronskian (secondJetPolynomial r a0 a1 a2 tail) D).derivative.eval r = 0) ↔
      (a1 = a0 * D.derivative.eval r / D.eval r ∧
        a2 = a0 * D.derivative.derivative.eval r / (2 * D.eval r)) := by
  rw [double_Wronskian_root_iff_jets _ _ _ hD]
  simp only [secondJetPolynomial_eval, secondJetPolynomial_derivative_eval,
    secondJetPolynomial_second_derivative_eval]
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  simp only [eq_div_iff (mul_ne_zero htwo hD), eq_div_iff hD]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linear_combination h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linear_combination h2⟩

#assert_trust kernel secondJetPolynomial_eval
#assert_trust kernel secondJetPolynomial_derivative_eval
#assert_trust kernel secondJetPolynomial_second_derivative_eval
#assert_trust kernel polynomialWronskian_derivative
#assert_trust kernel double_Wronskian_root_iff_jets
#assert_trust kernel secondJetPolynomial_double_root_iff
#print axioms secondJetPolynomial_double_root_iff
end NLA.Proofs.TR26
