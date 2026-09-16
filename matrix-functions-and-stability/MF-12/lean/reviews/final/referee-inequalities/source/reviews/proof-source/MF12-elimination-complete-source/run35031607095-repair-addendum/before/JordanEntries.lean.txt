/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
The binomial formula is derived from actual matrix multiplication, one
superdiagonal column at a time; no spectral or Jordan-form axiom is used.
-/
import NLA.MF12.Words
import NLA.MF12.Norms
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

namespace NLA.MF12

lemma mul_upperShift_zero_col {d : ℕ} (A : Square d) (r s : Fin d) (hs : s.val = 0) :
    (A * upperShift d) r s = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hk : k.val + 1 ≠ s.val := by omega
  simp [upperShift, hk]

lemma mul_upperShift_pos_col {d : ℕ} (A : Square d) (r s : Fin d) (hs : 0 < s.val) :
    (A * upperShift d) r s = A r ⟨s.val - 1, by omega⟩ := by
  let j : Fin d := ⟨s.val - 1, by omega⟩
  change (A * upperShift d) r s = A r j
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · have hjs : j.val + 1 = s.val := by dsimp [j]; omega
    simp [upperShift, hjs]
  · intro k _ hkj
    have hk : k.val + 1 ≠ s.val := by
      intro he
      apply hkj
      apply Fin.ext
      dsimp only [j]
      omega
    simp [upperShift, hk]
  · intro hn
    exact False.elim (hn (Finset.mem_univ j))

theorem jordan_entries (m n : ℕ) (r s : Fin (m + 1)) :
    (jordanMatrix m ^ n) r s =
      if r.val ≤ s.val then (Nat.choose n (s.val - r.val) : ℝ) else 0 := by
  induction n generalizing r s with
  | zero =>
      rw [pow_zero, Matrix.one_apply]
      by_cases hrs : r = s
      · subst s
        simp
      · by_cases hle : r.val ≤ s.val
        · have hlt : r.val < s.val := Nat.lt_of_le_of_ne hle (fun h => hrs (Fin.ext h))
          have hdiff : 0 < s.val - r.val := by omega
          simp [hrs, hle, Nat.choose_eq_zero_of_lt hdiff]
        · simp [hrs, hle]
  | succ n ih =>
      rw [pow_succ]
      change (jordanMatrix m ^ n * (1 + upperShift (m + 1))) r s = _
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
      by_cases hs0 : s.val = 0
      · rw [mul_upperShift_zero_col _ r s hs0, add_zero, ih]
        by_cases hr0 : r.val = 0
        · simp [hr0, hs0]
        · have hr : ¬ r.val ≤ s.val := by omega
          simp [hr]
      · have hs : 0 < s.val := Nat.pos_of_ne_zero hs0
        let j : Fin (m + 1) := ⟨s.val - 1, by omega⟩
        have hmul : (jordanMatrix m ^ n * upperShift (m + 1)) r s =
            (jordanMatrix m ^ n) r j := mul_upperShift_pos_col _ r s hs
        rw [hmul, ih, ih]
        by_cases hrs : r.val < s.val
        · have hrj : r.val ≤ j.val := by dsimp only [j]; omega
          have hdiff : s.val - r.val = (j.val - r.val) + 1 := by dsimp only [j]; omega
          simp only [if_pos hrs.le, if_pos hrj, hdiff, Nat.choose_succ_succ, Nat.cast_add] <;> ring
        · by_cases heq : r.val = s.val
          · have hrj : ¬ r.val ≤ j.val := by dsimp only [j]; omega
            simp [heq, hrj]
          · have hnot : ¬ r.val ≤ s.val := by omega
            have hrj : ¬ r.val ≤ j.val := by dsimp only [j]; omega
            simp [hnot, hrj]

lemma jordan_power_diagonal (m n : ℕ) (r : Fin (m + 1)) :
    (jordanMatrix m ^ n) r r = 1 := by simp [jordan_entries]

lemma jordanMatrix_ne_zero (m : ℕ) : jordanMatrix m ≠ 0 := by
  intro hz
  have he : (jordanMatrix m ^ 1) (0 : Fin (m + 1)) 0 = 1 := jordan_power_diagonal m 1 0
  simpa only [pow_one, hz, Matrix.zero_apply, zero_ne_one] using he

lemma binaryProduct_with_zero {d : ℕ} (A : Square d) (w : List Bool) :
    binaryProduct A 0 w = if true ∈ w then 0 else A ^ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
      rw [binaryProduct_cons, ih]
      cases b <;> by_cases ht : true ∈ w <;> simp [ht, pow_succ]

lemma zero_pair_growth {d : ℕ} (A : Square d) (n : ℕ) :
    familyGrowth (pairFamily A 0) n = spectralNorm (A ^ n) := by
  apply le_antisymm
  · apply familyGrowth_le_of_binary
    intro w hwn
    rw [binaryProduct_with_zero]
    by_cases ht : true ∈ w
    · rw [if_pos ht]
      simpa [spectralNorm] using spectralNorm_nonneg (A ^ n)
    · rw [if_neg ht, hwn]
  · have h := binaryProduct_le_familyGrowth A 0 (List.replicate n false)
    simpa only [binaryProduct_replicate_false, List.length_replicate] using h

theorem integer_family_growth (m : ℕ) (n : ℕ) (hn : 1 ≤ n) :
    familyGrowth (pairFamily (jordanMatrix m) 0) n = spectralNorm (jordanMatrix m ^ n) :=
  zero_pair_growth (jordanMatrix m) n

#assert_trust kernel jordan_entries
#assert_trust kernel integer_family_growth
#print axioms jordan_entries
#print axioms integer_family_growth

end NLA.MF12
