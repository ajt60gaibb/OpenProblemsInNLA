import NLA.Proofs.TR04.SVDRank

/-! The ordered weighted-energy inequality with an exact nonnegative defect.
Its equality conclusions retain the entire threshold eigenspace, so they do
not require a spectral gap or an eigenbasis aligned with a comparator. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators

namespace NLA.Proofs.TR04.SVD

def prefixEnergy {n : ℕ} (a : Fin n → ℝ) (r : ℕ) : ℝ :=
  ∑ i, if i.val < r then a i else 0

def weightDefect {n : ℕ} (a w : Fin n → ℝ) (r : Fin n) (i : Fin n) : ℝ :=
  if i.val < r.val then (a i - a r) * (1 - w i) else (a r - a i) * w i

theorem prefix_count {n : ℕ} (r : Fin n) :
    (∑ i : Fin n, if i.val < r.val then (1 : ℝ) else 0) = r.val := by
  rw [sum_fin_truncate (Nat.le_of_lt r.isLt)]
  · simp
  · intro i hi
    simp [Nat.not_lt.mpr hi]

theorem weighted_prefix_defect {n : ℕ} (a w : Fin n → ℝ) (r : Fin n) :
    prefixEnergy a r.val - (∑ i, a i * w i) =
      a r * ((r.val : ℝ) - ∑ i, w i) + ∑ i, weightDefect a w r i := by
  have hterm (i : Fin n) :
      (if i.val < r.val then a i else 0) - a i * w i =
        a r * ((if i.val < r.val then (1 : ℝ) else 0) - w i) +
          weightDefect a w r i := by
    unfold weightDefect
    split_ifs <;> ring
  unfold prefixEnergy
  rw [← Finset.sum_sub_distrib]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, prefix_count]

theorem weightDefect_nonneg {n : ℕ} {a w : Fin n → ℝ} (r : Fin n)
    (ha : Antitone a) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (i : Fin n) :
    0 ≤ weightDefect a w r i := by
  unfold weightDefect
  split_ifs with hi
  · exact mul_nonneg (sub_nonneg.mpr (ha (Fin.le_iff_val_le_val.mpr hi.le)))
      (sub_nonneg.mpr (hw1 i))
  · exact mul_nonneg (sub_nonneg.mpr (ha (Fin.le_iff_val_le_val.mpr
      (Nat.le_of_not_gt hi)))) (hw0 i)

theorem weighted_prefix_le {n : ℕ} {a w : Fin n → ℝ} (r : Fin n)
    (ha : Antitone a) (ha0 : 0 ≤ a r) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∀ i, w i ≤ 1) (hwr : ∑ i, w i ≤ r.val) :
    (∑ i, a i * w i) ≤ prefixEnergy a r.val := by
  have hdef := weighted_prefix_defect a w r
  have hnon : 0 ≤ ∑ i, weightDefect a w r i :=
    Finset.sum_nonneg fun i _ => weightDefect_nonneg r ha hw0 hw1 i
  have hdim := mul_nonneg ha0 (sub_nonneg.mpr hwr)
  linarith

/-- Exact maximal captured energy forces full use of the rank allowance and
weight one strictly above, and zero strictly below, the boundary value. -/
theorem weighted_prefix_eq_support {n : ℕ} {a w : Fin n → ℝ} (r : Fin n)
    (ha : Antitone a) (ha0 : 0 < a r) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∀ i, w i ≤ 1) (hwr : ∑ i, w i ≤ r.val)
    (heq : (∑ i, a i * w i) = prefixEnergy a r.val) :
    (∑ i, w i) = r.val ∧
      (∀ i, a r < a i → w i = 1) ∧ (∀ i, a i < a r → w i = 0) := by
  have hd := weighted_prefix_defect a w r
  have hdn (i : Fin n) : 0 ≤ weightDefect a w r i :=
    weightDefect_nonneg r ha hw0 hw1 i
  have hsum : 0 ≤ ∑ i, weightDefect a w r i := Finset.sum_nonneg fun i _ => hdn i
  have hmul : 0 ≤ a r * ((r.val : ℝ) - ∑ i, w i) :=
    mul_nonneg ha0.le (sub_nonneg.mpr hwr)
  have hdim : (∑ i, w i) = r.val := by nlinarith
  have hzero : ∑ i, weightDefect a w r i = 0 := by nlinarith
  have hdi (i : Fin n) : weightDefect a w r i = 0 := by
    have hle := Finset.single_le_sum (fun j _ => hdn j) (Finset.mem_univ i)
    rw [hzero] at hle
    exact le_antisymm hle (hdn i)
  refine ⟨hdim, ?_, ?_⟩
  · intro i hi
    have hir : i.val < r.val := by
      by_contra hn
      have hai := ha (Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hn))
      linarith
    have hz := hdi i
    rw [weightDefect, if_pos hir] at hz
    have := hw1 i
    nlinarith
  · intro i hi
    have hri : ¬ i.val < r.val := by
      intro hir
      have hai := ha (Fin.le_iff_val_le_val.mpr hir.le)
      linarith
    have hz := hdi i
    rw [weightDefect, if_neg hri] at hz
    have := hw0 i
    nlinarith

#assert_trust kernel weighted_prefix_le
#assert_trust kernel weighted_prefix_eq_support
#print axioms weighted_prefix_eq_support

end NLA.Proofs.TR04.SVD
