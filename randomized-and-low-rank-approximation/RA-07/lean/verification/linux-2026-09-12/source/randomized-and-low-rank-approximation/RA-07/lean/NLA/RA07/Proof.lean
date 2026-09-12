/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Complete formal proof of Matthew J. Colbrook's affirmative resolution of RA-07.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.RA07.Roots
import NLA.RA07.Sums
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Polynomial Classical
noncomputable section

namespace NLA.RA07
open Polynomial

/-- The exact original ratios are ratios of consecutive actual derivatives. -/
theorem error_as_derivative_ratio {n : ℕ} (lam : Fin n → ℝ) (k : ℕ) :
    errorSequence lam k =
      (iteratedGeneratingDerivative lam (k + 1)).eval 0 /
        (iteratedGeneratingDerivative lam k).eval 0 := by
  rw [(generating_derivative_values_proved lam (k + 1)).2,
    (generating_derivative_values_proved lam k).2]
  have hfact : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [Nat.factorial_succ, Nat.cast_mul]
  rw [show ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) * elementarySymmetric lam (k + 1) =
    (k.factorial : ℝ) * (((k + 1 : ℕ) : ℝ) * elementarySymmetric lam (k + 1)) by ring]
  rw [mul_div_mul_left _ _ hfact]
  rfl

/-- Constant scaling cancels from every shifted ratio, even at zero numerators. -/
theorem shifted_error_ratio {n m : ℕ} (lam : Fin n → ℝ) (d : ℕ) (c : ℝ)
    (μ : Fin m → ℝ) (hc : c ≠ 0)
    (hfac : iteratedGeneratingDerivative lam d = C c * generatingPolynomial μ)
    (k : ℕ) : errorSequence lam (d + k) = errorSequence μ k := by
  have hshift (r : ℕ) : iteratedGeneratingDerivative lam (d + r) =
      C c * iteratedGeneratingDerivative μ r := by
    dsimp only [iteratedGeneratingDerivative] at hfac ⊢
    rw [Nat.add_comm d r, Function.iterate_add_apply, hfac, iterate_derivative_C_mul]
  rw [error_as_derivative_ratio, Nat.add_assoc, hshift (k + 1), hshift k]
  rw [eval_mul, eval_C, eval_mul, eval_C, mul_div_mul_left _ _ hc]
  exact (error_as_derivative_ratio μ k).symm

theorem initial_second_difference {m : ℕ} (μ : Fin m → ℝ)
    (hm : 2 ≤ m) (hμ : ∀ a, 0 < μ a) :
    errorSequence μ 0 - 2 * errorSequence μ 1 + errorSequence μ 2 =
      2 * pairGap μ / certificateDenominator μ := by
  have h0 : (generatingPolynomial μ).eval 0 = 1 := by
    simp only [generatingPolynomial, eval_prod, eval_add, eval_one, eval_mul,
      eval_C, eval_X, mul_zero, add_zero, Finset.prod_const_one]
  have hder := generating_derivatives μ
  have hD := (power_sum_certificate_proved μ hm hμ).1
  have hne := mul_ne_zero_iff.mp (ne_of_gt hD)
  change powerSum μ 1 ≠ 0 ∧ powerSum μ 1 ^ 2 - powerSum μ 2 ≠ 0 at hne
  simp only [error_as_derivative_ratio, iteratedGeneratingDerivative,
    Function.iterate_succ_apply', Function.iterate_zero_apply,
    h0, hder.1, hder.2.1, hder.2.2, div_one]
  rw [← pair_gap_identity μ, certificateDenominator]
  field_simp [hne.1, hne.2]
  ring

theorem second_difference_certificate_proved {n : ℕ} (hn : 3 ≤ n)
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (j : ℕ) (hj : 2 ≤ j) (hjn : j ≤ n - 1) :
    ∃ μ : Fin (n - (j - 1)) → ℝ, (∀ a, 0 < μ a) ∧
      iteratedGeneratingDerivative lam (j - 1) =
        C ((iteratedGeneratingDerivative lam (j - 1)).eval 0) * generatingPolynomial μ ∧
      0 < certificateDenominator μ ∧
      errorSequence lam (j - 1) - 2 * errorSequence lam j + errorSequence lam (j + 1) =
        2 * pairGap μ / certificateDenominator μ := by
  have hd : j - 1 ≤ n := by omega
  have hm : 2 ≤ n - (j - 1) := by omega
  obtain ⟨hp, _, μ, hμ, hfac⟩ := positive_derivative_factorization_proved lam hlam (j - 1) hd
  refine ⟨μ, hμ, hfac, (power_sum_certificate_proved μ hm hμ).1, ?_⟩
  have hshift := shifted_error_ratio lam (j - 1)
    ((iteratedGeneratingDerivative lam (j - 1)).eval 0) μ hp.ne' hfac
  have h0 : errorSequence lam (j - 1) = errorSequence μ 0 := by
    simpa only [Nat.add_zero] using hshift 0
  have h1 : errorSequence lam j = errorSequence μ 1 := by
    simpa only [show j - 1 + 1 = j by omega] using hshift 1
  have h2 : errorSequence lam (j + 1) = errorSequence μ 2 := by
    simpa only [show j - 1 + 2 = j + 1 by omega] using hshift 2
  rw [h0, h1, h2]
  exact initial_second_difference μ hm hμ

theorem errorSequence_convex_proved : ConvexityConjecture := by
  intro n hn lam hlam j hj hjn
  obtain ⟨μ, hμ, _, hD, heq⟩ := second_difference_certificate_proved hn lam hlam j hj hjn
  have hm : 2 ≤ n - (j - 1) := by omega
  rw [heq]
  exact div_nonneg (mul_nonneg (by norm_num) (power_sum_certificate_proved μ hm hμ).2.2) hD.le

-- The argument is exact algebra and root geometry. LeanCert audits the kernel trust
-- boundary; no artificial interval calculation is added to this nonnumerical proof.
#assert_trust kernel elementary_values_proved
#assert_trust kernel generating_derivative_values_proved
#assert_trust kernel positive_derivative_factorization_proved
#assert_trust kernel power_sum_certificate_proved
#assert_trust kernel second_difference_certificate_proved
#assert_trust kernel errorSequence_convex_proved
#print axioms elementary_values_proved
#print axioms generating_derivative_values_proved
#print axioms positive_derivative_factorization_proved
#print axioms power_sum_certificate_proved
#print axioms second_difference_certificate_proved
#print axioms errorSequence_convex_proved

end NLA.RA07
