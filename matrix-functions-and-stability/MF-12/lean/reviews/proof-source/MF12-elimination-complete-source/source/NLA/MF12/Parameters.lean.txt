/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
-/
import NLA.MF12.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF12

lemma baseLambda_pos : 0 < baseLambda := by norm_num [baseLambda]
lemma baseLambda_lt_one : baseLambda < 1 := by norm_num [baseLambda]

lemma baseMu_pos (α : ℝ) : 0 < baseMu α :=
  Real.rpow_pos_of_pos baseLambda_pos _

lemma baseMu_lt_one (α : ℝ) (hα1 : α < 1) : baseMu α < 1 :=
  Real.rpow_lt_one baseLambda_pos.le baseLambda_lt_one (sub_pos.mpr hα1)

lemma fractionalPowerBound_ge_one (α : ℝ) (hα1 : α < 1) :
    1 ≤ fractionalPowerBound α := by
  have hm := baseMu_pos α
  have hp : 0 < 1 - baseMu α := sub_pos.mpr (baseMu_lt_one α hα1)
  change 1 ≤ (1 - baseMu α)⁻¹
  rw [← one_div, le_div_iff₀ hp]
  linarith

theorem fractional_parameters (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < baseLambda ∧ baseLambda < baseMu α ∧ baseMu α < 1 ∧
    1 ≤ fractionalPowerBound α ∧
    0 < fractionalLower α ∧ fractionalLower α ≤ fractionalUpper α := by
  have hmu : baseLambda < baseMu α :=
    Real.self_lt_rpow_of_lt_one baseLambda_pos baseLambda_lt_one (by linarith)
  have hH := fractionalPowerBound_ge_one α hα1
  have hc : 0 < fractionalLower α :=
    div_pos (Real.rpow_pos_of_pos baseLambda_pos α) (by norm_num)
  have hc1 : fractionalLower α < 1 := by
    have hpow := Real.rpow_lt_one baseLambda_pos.le baseLambda_lt_one hα
    change baseLambda ^ α / 10 < 1
    linarith
  refine ⟨baseLambda_pos, hmu, baseMu_lt_one α hα1, hH, hc, ?_⟩
  dsimp only [fractionalUpper]
  nlinarith [sq_nonneg (fractionalPowerBound α - 1)]

lemma loss_nonneg (q : ℕ) : 0 ≤ loss q :=
  mul_nonneg (Nat.cast_nonneg q) (pow_nonneg baseLambda_pos.le q)

lemma loss_le_quarter (q : ℕ) : loss q ≤ 1 / 4 := by
  induction q with
  | zero => norm_num [loss]
  | succ q ih =>
      by_cases hq0 : q = 0
      · subst q
        norm_num [loss, baseLambda]
      · have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq0
        have hp : 0 ≤ (1 / 4 : ℝ) ^ q := by positivity
        have hmul := mul_nonneg (sub_nonneg.mpr hq) hp
        dsimp only [loss, baseLambda] at ih ⊢
        rw [pow_succ]
        push_cast
        nlinarith

lemma loss_lt_one (q : ℕ) : loss q < 1 := lt_of_le_of_lt (loss_le_quarter q) (by norm_num)

lemma loss_pos (q : ℕ) (hq : 1 ≤ q) : 0 < loss q :=
  mul_pos (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
    (pow_pos baseLambda_pos q)

theorem loss_gain_bounds (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    loss 0 = 0 ∧ gain α 0 = 0 ∧
    (∀ q : ℕ, 1 ≤ q → 0 < loss q ∧ loss q ≤ 1 / 4) ∧
    ∀ q : ℕ, gain α q = Real.rpow (q : ℝ) α * Real.rpow (loss q) (1 - α) := by
  refine ⟨by simp [loss], by simp [gain], fun q hq => ⟨loss_pos q hq, loss_le_quarter q⟩, ?_⟩
  intro q
  have hqpow : (q : ℝ) ^ α * (q : ℝ) ^ (1 - α) = q := by
    rw [← Real.rpow_add_of_nonneg (Nat.cast_nonneg q) hα.le (sub_nonneg.mpr hα1.le)]
    simp
  calc
    gain α q = (q : ℝ) * Real.rpow (baseLambda ^ q) (1 - α) := by
      dsimp only [gain, baseMu]
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_pow_comm baseLambda_pos.le]
    _ = Real.rpow (q : ℝ) α * Real.rpow ((q : ℝ) * baseLambda ^ q) (1 - α) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow (Nat.cast_nonneg q) (pow_nonneg baseLambda_pos.le q)]
      rw [← mul_assoc, hqpow]
    _ = Real.rpow (q : ℝ) α * Real.rpow (loss q) (1 - α) := rfl

theorem bernoulli_loss (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell < 1) (k : ℕ) :
    (1 - ell) ^ k ≤ 1 / (1 + (k : ℝ) * ell) ∧
    ((1 / 4 : ℝ) ≤ (k : ℝ) * ell → (1 / 5 : ℝ) ≤ 1 - (1 - ell) ^ k) := by
  have hproduct : ∀ j : ℕ, (1 - ell) ^ j * (1 + (j : ℝ) * ell) ≤ 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hsmall : (1 - ell) * (1 + ((j : ℝ) + 1) * ell) ≤ 1 + (j : ℝ) * ell := by
          nlinarith [sq_nonneg ell, mul_nonneg (Nat.cast_nonneg j) (sq_nonneg ell)]
        calc
          (1 - ell) ^ (j + 1) * (1 + ((j + 1 : ℕ) : ℝ) * ell) =
              (1 - ell) ^ j * ((1 - ell) * (1 + ((j : ℝ) + 1) * ell)) := by
                rw [pow_succ]
                push_cast
                ring
          _ ≤ (1 - ell) ^ j * (1 + (j : ℝ) * ell) :=
            mul_le_mul_of_nonneg_left hsmall (pow_nonneg (sub_nonneg.mpr hell1.le) j)
          _ ≤ 1 := ih
  have hden : 0 < 1 + (k : ℝ) * ell := by positivity
  have hbound : (1 - ell) ^ k ≤ 1 / (1 + (k : ℝ) * ell) :=
    (le_div_iff₀ hden).mpr (hproduct k)
  refine ⟨hbound, ?_⟩
  intro hmass
  have hreciprocal : 1 / (1 + (k : ℝ) * ell) ≤ 4 / 5 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith

#assert_trust kernel fractional_parameters
#assert_trust kernel loss_gain_bounds
#assert_trust kernel bernoulli_loss
#print axioms fractional_parameters
#print axioms loss_gain_bounds
#print axioms bernoulli_loss

end NLA.MF12
