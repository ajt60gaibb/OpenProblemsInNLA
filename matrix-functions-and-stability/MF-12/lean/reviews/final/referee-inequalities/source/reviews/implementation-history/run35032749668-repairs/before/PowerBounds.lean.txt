/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
Bernoulli's elementary denominator bound controls every Jordan off-diagonal
power uniformly, avoiding a geometric-series or derivative computation.
-/
import NLA.MF12.MatrixAlgebra
import NLA.MF12.Parameters
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF12

lemma nat_mul_contraction_power (u : ℝ) (hu : 0 < u) (hu1 : u < 1) (q : ℕ) :
    (q : ℝ) * u ^ q ≤ (1 - u)⁻¹ := by
  have hδ : 0 < 1 - u := sub_pos.mpr hu1
  have hden : 0 < 1 + (q : ℝ) * (1 - u) := by positivity
  have hb := (bernoulli_loss (1 - u) hδ.le (by linarith) q).1
  have hb' : u ^ q ≤ 1 / (1 + (q : ℝ) * (1 - u)) := by
    simpa only [sub_sub_cancel] using hb
  have hp := (le_div_iff₀ hden).mp hb'
  rw [← one_div, le_div_iff₀ hδ]
  nlinarith [pow_nonneg hu.le q]

theorem fractional_powers_entry_bound (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (q : ℕ) (r s : Fin 6) :
    |(fractionalMatrix α ^ q) r s| ≤ fractionalPowerBound α := by
  have hH := fractionalPowerBound_ge_one α hα1
  have hzero : |(0 : ℝ)| ≤ fractionalPowerBound α := by
    rw [abs_zero]
    linarith
  have hone : |(1 : ℝ)| ≤ fractionalPowerBound α := by simpa only [abs_one] using hH
  have hLambdaPow : |baseLambda ^ q| ≤ fractionalPowerBound α := by
    rw [abs_of_nonneg (pow_nonneg baseLambda_pos.le q)]
    exact (pow_le_one₀ baseLambda_pos.le baseLambda_lt_one.le).trans hH
  have hμpow : |baseMu α ^ q| ≤ fractionalPowerBound α := by
    rw [abs_of_nonneg (pow_nonneg (baseMu_pos α).le q)]
    exact (pow_le_one₀ (baseMu_pos α).le (baseMu_lt_one α hα1).le).trans hH
  have hLambdaOff : |(q : ℝ) * baseLambda ^ q| ≤ fractionalPowerBound α := by
    rw [abs_of_nonneg (loss_nonneg q)]
    exact (loss_le_quarter q).trans ((by norm_num : (1 / 4 : ℝ) ≤ 1).trans hH)
  have hμoff : |(q : ℝ) * baseMu α ^ q| ≤ fractionalPowerBound α := by
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg q) (pow_nonneg (baseMu_pos α).le q))]
    exact nat_mul_contraction_power (baseMu α) (baseMu_pos α) (baseMu_lt_one α hα1) q
  rw [fractionalMatrix_power]
  fin_cases r <;> fin_cases s
  · change |(1 : ℝ)| ≤ fractionalPowerBound α
    exact hone
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(baseLambda ^ q : ℝ)| ≤ fractionalPowerBound α
    exact hLambdaPow
  · change |((q : ℝ) * baseLambda ^ q : ℝ)| ≤ fractionalPowerBound α
    exact hLambdaOff
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(baseLambda ^ q : ℝ)| ≤ fractionalPowerBound α
    exact hLambdaPow
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(baseMu α ^ q : ℝ)| ≤ fractionalPowerBound α
    exact hμpow
  · change |((q : ℝ) * baseMu α ^ q : ℝ)| ≤ fractionalPowerBound α
    exact hμoff
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(baseMu α ^ q : ℝ)| ≤ fractionalPowerBound α
    exact hμpow
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(0 : ℝ)| ≤ fractionalPowerBound α
    exact hzero
  · change |(1 : ℝ)| ≤ fractionalPowerBound α
    exact hone

#assert_trust kernel fractional_powers_entry_bound
#print axioms fractional_powers_entry_bound

end NLA.MF12
