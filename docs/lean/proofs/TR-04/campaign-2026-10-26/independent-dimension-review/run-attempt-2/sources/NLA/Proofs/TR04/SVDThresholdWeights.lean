import NLA.Proofs.TR04.SVDWeights

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD

def thresholdDefect {n : ℕ} (a w : Fin n → ℝ) (cut : ℕ) (tau : ℝ) (i : Fin n) : ℝ :=
  if i.val < cut then (a i - tau) * (1 - w i) else (tau - a i) * w i

theorem prefix_count_of_le {n cut : ℕ} (hc : cut ≤ n) :
    (∑ i : Fin n, if i.val < cut then (1 : ℝ) else 0) = cut := by
  rw [sum_fin_truncate hc]
  · simp
  · intro i hi
    simp [Nat.not_lt.mpr hi]

theorem weighted_threshold_defect {n cut : ℕ} (hc : cut ≤ n)
    (a w : Fin n → ℝ) (tau : ℝ) :
    prefixEnergy a cut - (∑ i, a i * w i) =
      tau * ((cut : ℝ) - ∑ i, w i) + ∑ i, thresholdDefect a w cut tau i := by
  have hterm (i : Fin n) :
      (if i.val < cut then a i else 0) - a i * w i =
        tau * ((if i.val < cut then (1 : ℝ) else 0) - w i) +
          thresholdDefect a w cut tau i := by
    unfold thresholdDefect
    split_ifs <;> ring
  unfold prefixEnergy
  rw [← Finset.sum_sub_distrib]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, prefix_count_of_le hc]

theorem thresholdDefect_nonneg {n cut : ℕ} {a w : Fin n → ℝ} {tau : ℝ}
    (habove : ∀ i, i.val < cut → tau ≤ a i)
    (hbelow : ∀ i, cut ≤ i.val → a i ≤ tau)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (i : Fin n) :
    0 ≤ thresholdDefect a w cut tau i := by
  unfold thresholdDefect
  split_ifs with hi
  · exact mul_nonneg (sub_nonneg.mpr (habove i hi)) (sub_nonneg.mpr (hw1 i))
  · exact mul_nonneg (sub_nonneg.mpr (hbelow i (Nat.le_of_not_gt hi))) (hw0 i)

theorem weighted_threshold_le {n cut : ℕ} (hc : cut ≤ n) {a w : Fin n → ℝ}
    {tau : ℝ} (htau : 0 ≤ tau)
    (habove : ∀ i, i.val < cut → tau ≤ a i)
    (hbelow : ∀ i, cut ≤ i.val → a i ≤ tau)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (hwr : ∑ i, w i ≤ cut) :
    (∑ i, a i * w i) ≤ prefixEnergy a cut := by
  have hd := weighted_threshold_defect hc a w tau
  have hsn : 0 ≤ ∑ i, thresholdDefect a w cut tau i :=
    Finset.sum_nonneg fun i _ => thresholdDefect_nonneg habove hbelow hw0 hw1 i
  have hdim := mul_nonneg htau (sub_nonneg.mpr hwr)
  linarith

theorem weighted_threshold_eq_support {n cut : ℕ} (hc : cut ≤ n) {a w : Fin n → ℝ}
    {tau : ℝ} (htau : 0 < tau)
    (habove : ∀ i, i.val < cut → tau ≤ a i)
    (hbelow : ∀ i, cut ≤ i.val → a i ≤ tau)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (hwr : ∑ i, w i ≤ cut)
    (heq : (∑ i, a i * w i) = prefixEnergy a cut) :
    (∑ i, w i) = cut ∧ (∀ i, tau < a i → w i = 1) ∧
      (∀ i, a i < tau → w i = 0) := by
  have hd := weighted_threshold_defect hc a w tau
  have hdn (i : Fin n) : 0 ≤ thresholdDefect a w cut tau i :=
    thresholdDefect_nonneg habove hbelow hw0 hw1 i
  have hsn : 0 ≤ ∑ i, thresholdDefect a w cut tau i := Finset.sum_nonneg fun i _ => hdn i
  have hmul : 0 ≤ tau * ((cut : ℝ) - ∑ i, w i) := mul_nonneg htau.le (sub_nonneg.mpr hwr)
  have hdim : (∑ i, w i) = cut := by nlinarith
  have hzero : ∑ i, thresholdDefect a w cut tau i = 0 := by nlinarith
  have hdi (i : Fin n) : thresholdDefect a w cut tau i = 0 := by
    have hle := Finset.single_le_sum (fun j _ => hdn j) (Finset.mem_univ i)
    rw [hzero] at hle
    exact le_antisymm hle (hdn i)
  refine ⟨hdim, ?_, ?_⟩
  · intro i hi
    have hir : i.val < cut := by
      by_contra hn
      exact (not_le_of_gt hi) (hbelow i (Nat.le_of_not_gt hn))
    have hz := hdi i
    rw [thresholdDefect, if_pos hir] at hz
    have := hw1 i
    nlinarith
  · intro i hi
    have hri : ¬ i.val < cut := fun hir => (not_le_of_gt hi) (habove i hir)
    have hz := hdi i
    rw [thresholdDefect, if_neg hri] at hz
    have := hw0 i
    nlinarith

#assert_trust kernel weighted_threshold_le
#assert_trust kernel weighted_threshold_eq_support
#print axioms weighted_threshold_eq_support
end NLA.Proofs.TR04.SVD
