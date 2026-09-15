/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.

A weighted shift has exactly one possible path for each matrix-power entry.
The proof reduces a matrix multiplication to one summand for arbitrary N.
-/
import NLA.MF24.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24
open scoped BigOperators

theorem height_shift_powers (N : ℕ) (h : Fin N → ℕ) (t : ℝ)
    (ht : 0 < t) (ℓ : ℕ) (r s : Fin N) :
    (heightShift h t ^ ℓ) r s =
      if s.val = r.val + ℓ then ((t ^ h s / t ^ h r : ℝ) : ℂ) else 0 := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  induction ℓ generalizing r s with
  | zero =>
      simp only [pow_zero, Matrix.one_apply, Nat.add_zero]
      by_cases hrs : r = s
      · subst s
        simp [pow_ne_zero _ (ne_of_gt ht)]
      · have hsr : s.val ≠ r.val := fun he => hrs (Fin.ext he.symm)
        simp [hrs, hsr]
  | succ ℓ ih =>
      rw [pow_succ, Matrix.mul_apply]
      by_cases hs : s.val = 0
      · have hzero : ∀ j : Fin N, j.val + 1 ≠ s.val := by
          intro j
          omega
        have hend : s.val ≠ r.val + (ℓ + 1) := by omega
        simp [heightShift, hzero, hend]
      · let k : Fin N := ⟨s.val - 1, by have := s.isLt; omega⟩
        have hks : k.val + 1 = s.val := by dsimp [k]; omega
        rw [Finset.sum_eq_single k]
        · rw [ih]
          simp only [heightShift, hks, if_true]
          by_cases hend : s.val = r.val + (ℓ + 1)
          · have hmid : k.val = r.val + ℓ := by omega
            simp only [hend, hmid, if_true]
            push_cast
            field_simp [htc] <;> ring
          · have hmid : k.val ≠ r.val + ℓ := by omega
            simp [hend, hmid]
        · intro j _ hjk
          have hj : j.val + 1 ≠ s.val := by
            intro he
            apply hjk
            apply Fin.ext
            omega
          simp [heightShift, hj]
        · intro hk
          exact False.elim (hk (Finset.mem_univ k))

lemma height_shift_nilpotent (N : ℕ) (h : Fin N → ℕ) (t : ℝ) (ht : 0 < t) :
    heightShift h t ^ N = 0 := by
  ext r s
  rw [height_shift_powers N h t ht N r s, if_neg (by have := s.isLt; omega)]
  rfl

lemma height_shift_real_nonnegative (N : ℕ) (h : Fin N → ℕ)
    (t : ℝ) (ht : 0 < t) (r s : Fin N) :
    (heightShift h t r s).im = 0 ∧ 0 ≤ (heightShift h t r s).re := by
  unfold heightShift
  split_ifs
  · simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
    exact div_nonneg (pow_nonneg ht.le _) (pow_nonneg ht.le _)
  · simp

#assert_trust kernel height_shift_powers
#print axioms height_shift_powers

end NLA.MF24
