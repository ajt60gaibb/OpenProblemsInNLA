/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
Every switching word is retained, including adjacent resets and zero endpoints.
-/
import NLA.MF12.Words
import NLA.MF12.MatrixAlgebra
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF12

@[simp] lemma gapWord_singleton (q : ℕ) : gapWord [q] = List.replicate q false := by
  simp [gapWord]

lemma gapWord_cons_cons (q r : ℕ) (qs : List ℕ) :
    gapWord (q :: r :: qs) = List.replicate q false ++ true :: gapWord (r :: qs) := by
  simp only [gapWord, List.map_cons, List.intersperse_cons_cons,
    List.flatten_cons, List.singleton_append]

lemma gapWord_increase_first (q : ℕ) (qs : List ℕ) :
    gapWord ((q + 1) :: qs) = false :: gapWord (q :: qs) := by
  cases qs with
  | nil => simp [List.replicate_succ]
  | cons r qs => simp only [gapWord_cons_cons, List.replicate_succ, List.cons_append]

theorem gap_decomposition (w : List Bool) :
    ∃ qs : List ℕ, qs ≠ [] ∧ gapWord qs = w ∧
      qs.sum + (qs.length - 1) = w.length := by
  induction w with
  | nil => exact ⟨[0], by simp, by simp, by simp⟩
  | cons b w ih =>
      obtain ⟨qs, hne, hword, hlength⟩ := ih
      cases qs with
      | nil => exact False.elim (hne rfl)
      | cons q qs =>
          cases b with
          | false =>
              refine ⟨(q + 1) :: qs, by simp, ?_, ?_⟩
              · rw [gapWord_increase_first, hword]
              · simp only [List.sum_cons, List.length_cons] at hlength ⊢
                omega
          | true =>
              refine ⟨0 :: q :: qs, by simp, ?_, ?_⟩
              · rw [gapWord_cons_cons]
                simpa only [List.replicate_zero, List.nil_append] using congrArg (List.cons true) hword
              · simp only [List.sum_cons, List.length_cons] at hlength ⊢
                omega

lemma binaryProduct_gap_head {d : ℕ} (A P : Square d) (q r : ℕ) (qs : List ℕ) :
    binaryProduct A P (gapWord (q :: r :: qs)) =
      binaryProduct A P (gapWord (r :: qs)) * P * A ^ q := by
  rw [gapWord_cons_cons, binaryProduct_append, binaryProduct_cons,
    binaryProduct_replicate_false]
  rfl

lemma compressedProduct_cons (α : ℝ) (q : ℕ) (qs : List ℕ) :
    compressedProduct α (q :: qs) = compressedProduct α qs * compressed α q := by
  simp only [compressedProduct, List.map_cons, matrixProduct_cons]

theorem reset_product_factorization (α : ℝ) (q₀ qlast : ℕ) (qs : List ℕ) :
    binaryProduct (fractionalMatrix α) resetMatrix (gapWord (q₀ :: (qs ++ [qlast]))) =
      fractionalMatrix α ^ qlast * sourceV * compressedProduct α qs *
        sourceU * fractionalMatrix α ^ q₀ := by
  induction qs generalizing q₀ with
  | nil =>
      simp only [List.nil_append, binaryProduct_gap_head, gapWord_singleton,
        binaryProduct_replicate_false, compressedProduct, List.map_nil,
        matrixProduct_nil, Matrix.mul_one, resetMatrix, Matrix.mul_assoc]
  | cons q qs ih =>
      rw [List.cons_append, binaryProduct_gap_head, ih q, compressedProduct_cons]
      simp only [compressed, resetMatrix, Matrix.mul_assoc]

lemma binaryProduct_flatten_replicate {d : ℕ} (A P : Square d) (w : List Bool) (k : ℕ) :
    binaryProduct A P (List.replicate k w).flatten = binaryProduct A P w ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, binaryProduct_append, ih, pow_succ]

lemma chosenRemainder_add_count (n : ℕ) :
    chosenRemainder n + chosenCount n * (chosenGap n + 1) = n := by
  have hle : chosenCount n * (chosenGap n + 1) ≤ n :=
    Nat.div_mul_le_self n (chosenGap n + 1)
  exact Nat.sub_add_cancel hle

theorem lower_word_exact (α : ℝ) (n : ℕ) :
    (lowerWord n).length = n ∧
    binaryProduct (fractionalMatrix α) resetMatrix (lowerWord n) =
      if n < 4 then fractionalMatrix α ^ n else
        fractionalMatrix α ^ chosenRemainder n *
          (resetMatrix * fractionalMatrix α ^ chosenGap n) ^ chosenCount n := by
  by_cases hn : n < 4
  · simp [lowerWord, hn]
  · simp only [lowerWord, if_neg hn]
    constructor
    · simpa only [List.length_append, List.length_flatten, List.map_replicate,
        List.sum_replicate, List.length_replicate, List.length_singleton,
        nsmul_eq_mul, add_comm] using chosenRemainder_add_count n
    · rw [binaryProduct_append, binaryProduct_replicate_false,
        binaryProduct_flatten_replicate, binaryProduct_append,
        binaryProduct_replicate_false]
      simp [binaryProduct_cons]

#assert_trust kernel gap_decomposition
#assert_trust kernel reset_product_factorization
#assert_trust kernel lower_word_exact
#print axioms gap_decomposition
#print axioms reset_product_factorization
#print axioms lower_word_exact

end NLA.MF12
