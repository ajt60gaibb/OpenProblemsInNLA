/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
The all-switching bound is an application of Mathlib's finite real Holder
inequality; no interval subdivision or sampled switching family is used.
-/
import NLA.MF12.Budgets
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

namespace NLA.MF12

lemma fractional_holder {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    (∑ i ∈ s, Real.rpow (f i) α * Real.rpow (g i) (1 - α)) ≤
      Real.rpow (∑ i ∈ s, f i) α * Real.rpow (∑ i ∈ s, g i) (1 - α) := by
  have hβ : 0 < 1 - α := sub_pos.mpr hα1
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s
    (f := fun i => Real.rpow (f i) α) (g := fun i => Real.rpow (g i) (1 - α))
    (Real.HolderConjugate.inv_one_sub_inv hα hα1)
    (fun i _ => Real.rpow_nonneg (hf i) _) (fun i _ => Real.rpow_nonneg (hg i) _)
  have hfp (i : ι) : Real.rpow (Real.rpow (f i) α) α⁻¹ = f i :=
    Real.rpow_rpow_inv (hf i) hα.ne'
  have hgp (i : ι) : Real.rpow (Real.rpow (g i) (1 - α)) (1 - α)⁻¹ = g i :=
    Real.rpow_rpow_inv (hg i) hβ.ne'
  simpa only [hfp, hgp, one_div, inv_inv] using h

lemma sum_gap_values (qs : List ℕ) :
    (∑ i ∈ Finset.range qs.length, (qs.getD i 0 : ℝ)) = (qs.sum : ℝ) := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.sum_cons, Nat.cast_add]
      ring

lemma weighted_gain_identity (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (q : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    gain α q * w = Real.rpow ((q : ℝ) * w) α * Real.rpow (loss q * w) (1 - α) := by
  have hg := (loss_gain_bounds α hα hα1).2.2.2 q
  have hwp : Real.rpow w α * Real.rpow w (1 - α) = w := by
    rw [← Real.rpow_add_of_nonneg hw hα.le (sub_nonneg.mpr hα1.le)]
    simp
  rw [Real.mul_rpow (Nat.cast_nonneg q) hw, Real.mul_rpow (loss_nonneg q) hw]
  calc
    gain α q * w =
        (Real.rpow (q : ℝ) α * Real.rpow (loss q) (1 - α)) *
          (Real.rpow w α * Real.rpow w (1 - α)) := by rw [hwp, hg]
    _ = (Real.rpow (q : ℝ) α * Real.rpow w α) *
        (Real.rpow (loss q) (1 - α) * Real.rpow w (1 - α)) := by ring

theorem compressed_product_bound (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (qs : List ℕ) :
    0 ≤ offDiagonalBudget α qs ∧
    offDiagonalBudget α qs ≤ Real.rpow (qs.sum : ℝ) α := by
  refine ⟨offDiagonalBudget_nonneg α qs, ?_⟩
  let f : ℕ → ℝ := fun i => (qs.getD i 0 : ℝ) * tailWeight qs i
  let g : ℕ → ℝ := fun i => loss (qs.getD i 0) * tailWeight qs i
  have hf (i : ℕ) : 0 ≤ f i := mul_nonneg (Nat.cast_nonneg _) (tailWeight_bounds qs i).1
  have hg (i : ℕ) : 0 ≤ g i := mul_nonneg (loss_nonneg _) (tailWeight_bounds qs i).1
  have hF : (∑ i ∈ Finset.range qs.length, f i) ≤ (qs.sum : ℝ) := by
    rw [← sum_gap_values qs]
    apply Finset.sum_le_sum
    intro i _
    exact (mul_le_mul_of_nonneg_left (tailWeight_bounds qs i).2
      (Nat.cast_nonneg (qs.getD i 0))).trans_eq (mul_one _)
  have hG : (∑ i ∈ Finset.range qs.length, g i) ≤ 1 := by
    change (∑ i ∈ Finset.range qs.length, loss (qs.getD i 0) * tailWeight qs i) ≤ 1
    rw [loss_budget_identity]
    have h := (diagonalBudget_bounds qs).1
    linarith
  have hF0 : 0 ≤ ∑ i ∈ Finset.range qs.length, f i :=
    Finset.sum_nonneg (fun i _ => hf i)
  have hG0 : 0 ≤ ∑ i ∈ Finset.range qs.length, g i :=
    Finset.sum_nonneg (fun i _ => hg i)
  calc
    offDiagonalBudget α qs =
        ∑ i ∈ Finset.range qs.length, Real.rpow (f i) α * Real.rpow (g i) (1 - α) := by
      apply Finset.sum_congr rfl
      intro i _
      exact weighted_gain_identity α hα hα1 (qs.getD i 0) _ (tailWeight_bounds qs i).1
    _ ≤ Real.rpow (∑ i ∈ Finset.range qs.length, f i) α *
        Real.rpow (∑ i ∈ Finset.range qs.length, g i) (1 - α) :=
      fractional_holder _ f g hf hg α hα hα1
    _ ≤ Real.rpow (qs.sum : ℝ) α * 1 :=
      mul_le_mul (Real.rpow_le_rpow hF0 hF hα.le)
        (Real.rpow_le_one hG0 hG (sub_nonneg.mpr hα1.le))
        (Real.rpow_nonneg hG0 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = Real.rpow (qs.sum : ℝ) α := mul_one _

#assert_trust kernel compressed_product_bound
#print axioms compressed_product_bound

end NLA.MF12
