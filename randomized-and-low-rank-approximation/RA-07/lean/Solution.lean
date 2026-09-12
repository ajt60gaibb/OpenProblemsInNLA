/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Reviewed exports for Matthew J. Colbrook's affirmative resolution of RA-07.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.RA07.Proof

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Polynomial

namespace NLA.RA07

/-- The canonical endpoint conventions and denominator positivity are conclusions. -/
theorem elementary_values {n : ℕ} (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i) :
    elementarySymmetric lam 0 = 1 ∧
    (∀ j : ℕ, n < j → elementarySymmetric lam j = 0) ∧
    (∀ j : ℕ, j ≤ n → 0 < elementarySymmetric lam j) := by
  exact elementary_values_proved lam hlam

/-- Both coefficients and actual iterated derivatives recover the subset sums. -/
theorem generating_derivative_values {n : ℕ} (lam : Fin n → ℝ) (j : ℕ) :
    (generatingPolynomial lam).coeff j = elementarySymmetric lam j ∧
    (iteratedGeneratingDerivative lam j).eval 0 =
      (j.factorial : ℝ) * elementarySymmetric lam j := by
  exact generating_derivative_values_proved lam j

/-- An unconditional exact factorization of every relevant actual derivative,
including all multiplicities; its degree and nonzero scale are also proved. -/
theorem positive_derivative_factorization {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (d : ℕ) (hd : d ≤ n) :
    0 < (iteratedGeneratingDerivative lam d).eval 0 ∧
    (iteratedGeneratingDerivative lam d).natDegree = n - d ∧
    ∃ μ : Fin (n - d) → ℝ, (∀ a, 0 < μ a) ∧
      iteratedGeneratingDerivative lam d =
        Polynomial.C ((iteratedGeneratingDerivative lam d).eval 0) *
          generatingPolynomial μ := by
  exact positive_derivative_factorization_proved lam hlam d hd

/-- The exact positive denominator and nonnegative pair certificate for any
positive tuple of length at least two, without assuming distinct entries. -/
theorem power_sum_certificate {m : ℕ} (μ : Fin m → ℝ)
    (hm : 2 ≤ m) (hμ : ∀ a, 0 < μ a) :
    0 < certificateDenominator μ ∧
    powerSum μ 1 * powerSum μ 3 - powerSum μ 2 ^ 2 = pairGap μ ∧
    0 ≤ pairGap μ := by
  exact power_sum_certificate_proved μ hm hμ

/-- The certificate is derived for the actual original ratios and the actual
derivative of order `j-1`; no factorization or gap identity is a premise. -/
theorem second_difference_certificate {n : ℕ} (hn : 3 ≤ n)
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (j : ℕ) (hj : 2 ≤ j) (hjn : j ≤ n - 1) :
    ∃ μ : Fin (n - (j - 1)) → ℝ, (∀ a, 0 < μ a) ∧
      iteratedGeneratingDerivative lam (j - 1) =
        Polynomial.C ((iteratedGeneratingDerivative lam (j - 1)).eval 0) *
          generatingPolynomial μ ∧
      0 < certificateDenominator μ ∧
      errorSequence lam (j - 1) - 2 * errorSequence lam j + errorSequence lam (j + 1) =
        2 * pairGap μ / certificateDenominator μ := by
  exact second_difference_certificate_proved hn lam hlam j hj hjn

/-- Affirmative solution of the complete original RA-07 assertion. -/
theorem errorSequence_convex : ConvexityConjecture := by
  exact errorSequence_convex_proved

#assert_trust kernel elementary_values
#assert_trust kernel generating_derivative_values
#assert_trust kernel positive_derivative_factorization
#assert_trust kernel power_sum_certificate
#assert_trust kernel second_difference_certificate
#assert_trust kernel errorSequence_convex
#print axioms elementary_values
#print axioms generating_derivative_values
#print axioms positive_derivative_factorization
#print axioms power_sum_certificate
#print axioms second_difference_certificate
#print axioms errorSequence_convex

end NLA.RA07
