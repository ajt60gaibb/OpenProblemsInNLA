/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact algebra for Matthew J. Colbrook's affirmative resolution of RA-07.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.RA07.Definitions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped BigOperators Polynomial Classical
noncomputable section

namespace NLA.RA07
open Polynomial

theorem elementary_values_proved {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) :
    elementarySymmetric lam 0 = 1 ∧
    (∀ j : ℕ, n < j → elementarySymmetric lam j = 0) ∧
    (∀ j : ℕ, j ≤ n → 0 < elementarySymmetric lam j) := by
  refine ⟨by simp [elementarySymmetric], ?_, ?_⟩
  · intro j hj
    have he : (Finset.univ : Finset (Fin n)).powersetCard j = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simpa using hj)
    simp [elementarySymmetric, he]
  · intro j hj
    apply Finset.sum_pos
    · intro S _
      exact Finset.prod_pos fun i _ => hlam i
    · exact Finset.powersetCard_nonempty.mpr (by simpa using hj)

theorem generating_coeff {n : ℕ} (lam : Fin n → ℝ) (j : ℕ) :
    (generatingPolynomial lam).coeff j = elementarySymmetric lam j := by
  rw [generatingPolynomial, Finset.prod_one_add]
  rw [elementarySymmetric, Finset.powersetCard_eq_filter, Finset.sum_filter]
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro S _
  have hp : (∏ i ∈ S, C (lam i) * X) = C (∏ i ∈ S, lam i) * X ^ S.card := by
    simp [Finset.prod_mul_distrib]
  rw [hp, coeff_C_mul_X_pow]
  simp only [eq_comm]

theorem generating_derivative_values_proved {n : ℕ} (lam : Fin n → ℝ) (j : ℕ) :
    (generatingPolynomial lam).coeff j = elementarySymmetric lam j ∧
    (iteratedGeneratingDerivative lam j).eval 0 =
      (j.factorial : ℝ) * elementarySymmetric lam j := by
  refine ⟨generating_coeff lam j, ?_⟩
  rw [iteratedGeneratingDerivative, ← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
  simp [generating_coeff, Nat.descFactorial_self, nsmul_eq_mul]

end NLA.RA07
