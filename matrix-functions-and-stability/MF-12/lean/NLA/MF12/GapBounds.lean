/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
The lower-word gap is an exact natural logarithm. All floor estimates are
proved in the natural numbers before a single rational inequality is cast.
-/
import NLA.MF12.Gaps
import NLA.MF12.Parameters
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF12

lemma two_mul_succ_le_four_pow (q : ℕ) (hq : 1 ≤ q) : 2 * (q + 1) ≤ 4 ^ q := by
  have h : ∀ j : ℕ, 2 * (j + 2) ≤ 4 ^ (j + 1) := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
        rw [pow_succ]
        nlinarith
  cases q with
  | zero => omega
  | succ q => simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using h q

theorem logarithmic_gap_bounds (n : ℕ) (hn : 4 ≤ n) :
    1 ≤ chosenGap n ∧ 1 ≤ chosenCount n ∧
    4 ^ chosenGap n ≤ n ∧ n < 4 ^ (chosenGap n + 1) ∧
    2 * (chosenGap n + 1) ≤ 4 ^ chosenGap n ∧
    chosenRemainder n + chosenCount n * (chosenGap n + 1) = n ∧
    (1 / 4 : ℝ) ≤ (chosenCount n : ℝ) * loss (chosenGap n) := by
  let q := chosenGap n
  let k := chosenCount n
  have hq : 1 ≤ q := Nat.log_pos (by norm_num : 1 < 4) hn
  have hpow : 4 ^ q ≤ n := Nat.pow_log_le_self 4 (by omega)
  have hpowNext : n < 4 ^ (q + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) n
  have hshort : 2 * (q + 1) ≤ 4 ^ q := two_mul_succ_le_four_pow q hq
  have hqn : q + 1 ≤ n := by omega
  have hk : 1 ≤ k := by
    change 1 ≤ n / (q + 1)
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [one_mul] using hqn)
  have hmod : n % (q + 1) < q + 1 := Nat.mod_lt _ (by omega)
  have hmodEq : n % (q + 1) + (q + 1) * k = n := Nat.mod_add_div n (q + 1)
  have hdivision : n < (k + 1) * (q + 1) := by nlinarith
  have hkdouble : k + 1 ≤ 2 * k := by omega
  have hqdouble : q + 1 ≤ 2 * q := by omega
  have hfirst := Nat.mul_le_mul_right (q + 1) hkdouble
  have hsecond := Nat.mul_le_mul_left (2 * k) hqdouble
  have hmass : 4 ^ q ≤ 4 * k * q := by nlinarith
  have hmassR : (4 : ℝ) ^ q ≤ 4 * (k : ℝ) * (q : ℝ) := by exact_mod_cast hmass
  have hpowR : 0 < (4 : ℝ) ^ q := by positivity
  refine ⟨hq, hk, hpow, hpowNext, hshort, chosenRemainder_add_count n, ?_⟩
  calc
    (1 / 4 : ℝ) ≤ ((k : ℝ) * (q : ℝ)) / (4 : ℝ) ^ q := by
      apply (le_div_iff₀ hpowR).mpr
      nlinarith
    _ = (chosenCount n : ℝ) * loss (chosenGap n) := by
      change ((k : ℝ) * (q : ℝ)) / (4 : ℝ) ^ q = (k : ℝ) * ((q : ℝ) * baseLambda ^ q)
      rw [baseLambda, div_pow, one_pow]
      ring

#assert_trust kernel logarithmic_gap_bounds
#print axioms logarithmic_gap_bounds

end NLA.MF12
