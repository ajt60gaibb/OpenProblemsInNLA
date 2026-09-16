/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
All formulas include empty switching lists and arbitrary zero gaps.
-/
import NLA.MF12.Words
import NLA.MF12.Parameters
import NLA.MF12.MatrixAlgebra
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

namespace NLA.MF12

@[simp] lemma diagonalBudget_nil : diagonalBudget [] = 1 := rfl

lemma diagonalBudget_cons (q : ℕ) (qs : List ℕ) :
    diagonalBudget (q :: qs) = (1 - loss q) * diagonalBudget qs := rfl

@[simp] lemma tailWeight_cons_zero (q : ℕ) (qs : List ℕ) :
    tailWeight (q :: qs) 0 = diagonalBudget qs := rfl

lemma tailWeight_cons_succ (q : ℕ) (qs : List ℕ) (i : ℕ) :
    tailWeight (q :: qs) (i + 1) = tailWeight qs i := rfl

lemma diagonalBudget_bounds (qs : List ℕ) : 0 ≤ diagonalBudget qs ∧ diagonalBudget qs ≤ 1 := by
  induction qs with
  | nil => norm_num [diagonalBudget]
  | cons q qs ih =>
      rw [diagonalBudget_cons]
      have ha : 0 ≤ 1 - loss q := sub_nonneg.mpr (loss_lt_one q).le
      refine ⟨mul_nonneg ha ih.1, ?_⟩
      calc
        (1 - loss q) * diagonalBudget qs ≤ (1 - loss q) * 1 :=
          mul_le_mul_of_nonneg_left ih.2 ha
        _ ≤ 1 := by have h := loss_nonneg q; linarith

lemma tailWeight_bounds (qs : List ℕ) (i : ℕ) :
    0 ≤ tailWeight qs i ∧ tailWeight qs i ≤ 1 := diagonalBudget_bounds (qs.drop (i + 1))

lemma loss_budget_identity (qs : List ℕ) :
    (∑ i ∈ Finset.range qs.length, loss (qs.getD i 0) * tailWeight qs i) =
      1 - diagonalBudget qs := by
  induction qs with
  | nil => simp [diagonalBudget]
  | cons q qs ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero,
        tailWeight_cons_succ, tailWeight_cons_zero]
      rw [ih, diagonalBudget_cons]
      ring

theorem telescoping_budget (qs : List ℕ) :
    0 ≤ diagonalBudget qs ∧ diagonalBudget qs ≤ 1 ∧
    (∀ i : ℕ, i < qs.length → 0 ≤ tailWeight qs i ∧ tailWeight qs i ≤ 1) ∧
    (∑ i ∈ Finset.range qs.length, loss (qs.getD i 0) * tailWeight qs i) =
      1 - diagonalBudget qs := by
  exact ⟨(diagonalBudget_bounds qs).1, (diagonalBudget_bounds qs).2,
    fun i _ => tailWeight_bounds qs i, loss_budget_identity qs⟩

@[simp] lemma offDiagonalBudget_nil (α : ℝ) : offDiagonalBudget α [] = 0 := by
  simp [offDiagonalBudget]

lemma offDiagonalBudget_cons (α : ℝ) (q : ℕ) (qs : List ℕ) :
    offDiagonalBudget α (q :: qs) =
      offDiagonalBudget α qs + gain α q * diagonalBudget qs := by
  unfold offDiagonalBudget
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [List.getD_cons_succ, List.getD_cons_zero,
    tailWeight_cons_succ, tailWeight_cons_zero]

theorem compressed_product_formula (α : ℝ) (qs : List ℕ) :
    compressedProduct α qs = !![diagonalBudget qs, offDiagonalBudget α qs; 0, 1] := by
  induction qs with
  | nil =>
      simp only [compressedProduct, List.map_nil, matrixProduct_nil,
        diagonalBudget_nil, offDiagonalBudget_nil]
      ext r s
      fin_cases r <;> fin_cases s <;> norm_num [Matrix.one_apply]
  | cons q qs ih =>
      rw [compressedProduct, List.map_cons, matrixProduct_cons]
      change compressedProduct α qs * compressed α q = _
      rw [ih, compressed_powers, diagonalBudget_cons, offDiagonalBudget_cons]
      ext r s
      fin_cases r <;> fin_cases s
      all_goals
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        dsimp
        ring

lemma offDiagonalBudget_nonneg (α : ℝ) (qs : List ℕ) : 0 ≤ offDiagonalBudget α qs := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (baseMu_pos α).le _)
  · exact (tailWeight_bounds qs i).1

#assert_trust kernel telescoping_budget
#assert_trust kernel compressed_product_formula
#print axioms telescoping_budget
#print axioms compressed_product_formula

end NLA.MF12
