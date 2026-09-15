/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
-/
import NLA.MF24.Dimensions
import NLA.MF24.Powers
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24
open Polynomial
open scoped BigOperators

lemma stride_pos (m : ℕ) : 0 < stride m := by unfold stride; omega

lemma polyEval_testPolynomial {N : ℕ} (A : Square N) (m : ℕ) :
    polyEval A (testPolynomial m) = ∑ j ∈ Finset.Icc 1 m, A ^ (stride m * j) := by
  simp [polyEval, testPolynomial]

lemma testPolynomial_eval_zero (m : ℕ) : (testPolynomial m).eval 0 = 0 := by
  simp only [testPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_X_pow]
  apply Finset.sum_eq_zero
  intro j hj
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hpos : 0 < stride m * j := Nat.mul_pos (stride_pos m) (by omega)
  exact zero_pow (Nat.ne_of_gt hpos)

lemma testPolynomial_top_coefficient (m : ℕ) (hm : 1 ≤ m) :
    (testPolynomial m).coeff (stride m * m) = 1 := by
  simp only [testPolynomial, finsetSum_coeff]
  rw [Finset.sum_eq_single m]
  · simp
  · intro j hj hjm
    have hjlt : j < m := by have := (Finset.mem_Icc.mp hj).2; omega
    have hmul := Nat.mul_lt_mul_of_pos_left hjlt (stride_pos m)
    simp [coeff_X_pow, ne_of_gt hmul]
  · intro hmnot
    exact False.elim (hmnot (Finset.mem_Icc.mpr ⟨hm, le_rfl⟩))

theorem polynomial_degree_evaluation (m : ℕ) (hm : 2 ≤ m) :
    (testPolynomial m).eval 0 = 0 ∧
    (testPolynomial m).natDegree = dimension m - 1 ∧
    ∀ A : Square (dimension m),
      polyEval A (testPolynomial m) = ∑ j ∈ Finset.Icc 1 m, A ^ (stride m * j) := by
  refine ⟨testPolynomial_eval_zero m, ?_, fun A => polyEval_testPolynomial A m⟩
  rw [dimension_sub_one, Nat.mul_comm m (stride m)]
  apply le_antisymm
  · unfold testPolynomial
    apply natDegree_sum_le_of_forall_le
    intro j hj
    simp only [natDegree_X_pow]
    exact Nat.mul_le_mul_left (stride m) (Finset.mem_Icc.mp hj).2
  · apply le_natDegree_of_ne_zero
    rw [testPolynomial_top_coefficient m (by omega)]
    exact one_ne_zero

theorem polynomial_entries (m : ℕ) (hm : 2 ≤ m)
    (h : Fin (dimension m) → ℕ) (t : ℝ) (ht : 0 < t)
    (r s : Fin (dimension m)) :
    polyEval (heightShift h t) (testPolynomial m) r s =
      if r.val < s.val ∧ stride m ∣ s.val - r.val then
        ((t ^ h s / t ^ h r : ℝ) : ℂ) else 0 := by
  rw [polyEval_testPolynomial]
  simp only [Finset.sum_apply, height_shift_powers (dimension m) h t ht]
  have hD := stride_pos m
  have hsize := s.isLt
  rw [dimension_eq] at hsize
  by_cases hforward : r.val < s.val ∧ stride m ∣ s.val - r.val
  · obtain ⟨j, hj⟩ := hforward.2
    have hsj : s.val = r.val + stride m * j := by omega
    have hj1 : 1 ≤ j := by
      by_contra hn
      have hz : j = 0 := by omega
      simp only [hz, mul_zero, add_zero] at hsj
      omega
    have hjm : j ≤ m := by
      by_contra hn
      have hjlarge : m + 1 ≤ j := by omega
      have hprod := Nat.mul_le_mul_left (stride m) hjlarge
      nlinarith
    rw [if_pos hforward, Finset.sum_eq_single j]
    · simp [hsj]
    · intro k _ hkj
      have hsk : s.val ≠ r.val + stride m * k := by
        intro he
        have heq : stride m * k = stride m * j := by omega
        exact hkj (Nat.eq_of_mul_eq_mul_left hD heq)
      simp [hsk]
    · intro hjnot
      exact False.elim (hjnot (Finset.mem_Icc.mpr ⟨hj1, hjm⟩))
  · rw [if_neg hforward]
    apply Finset.sum_eq_zero
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hsj : s.val ≠ r.val + stride m * j := by
      intro he
      apply hforward
      refine ⟨?_, ⟨j, ?_⟩⟩
      · have hprod := Nat.mul_pos hD (show 0 < j by omega)
        omega
      · omega
    simp [hsj]

#assert_trust kernel polynomial_degree_evaluation
#assert_trust kernel polynomial_entries
#print axioms polynomial_degree_evaluation
#print axioms polynomial_entries

end NLA.MF24
