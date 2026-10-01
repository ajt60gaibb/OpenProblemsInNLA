import Mathlib

/-!
# Summing the replication deficits

One exceptional copy can spend the uniform surplus of all the endpoint copies.
This is the scalar algebra in the source replication argument; the number of
copies depends only on the two deficit constants.
-/

noncomputable section

namespace ProofProject

/-- A single deficient copy is absorbed by the remaining `r-1` copies. -/
theorem replication_deficit_sum {r : ℕ} (pivot : Fin r) (δ : Fin r → ℝ)
    {c C H : ℝ} (hH : 0 ≤ H) (hbudget : C ≤ ((r : ℝ) - 1) * c)
    (hpivot : -C * H ≤ δ pivot)
    (hother : ∀ l, l ≠ pivot → c * H ≤ δ l) :
    0 ≤ ∑ l, δ l := by
  classical
  have hsum : (∑ l ∈ Finset.univ.erase pivot, c * H) ≤
      ∑ l ∈ Finset.univ.erase pivot, δ l := by
    exact Finset.sum_le_sum fun l hl => hother l (Finset.mem_erase.mp hl).1
  have hr : 1 ≤ r := by have := pivot.isLt; omega
  have hcard : (Finset.univ.erase pivot).card = r - 1 := by simp
  simp only [Finset.sum_const, hcard, nsmul_eq_mul] at hsum
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr, Nat.cast_one]
  rw [hcast] at hsum
  have hfull := Finset.sum_erase_add (s := Finset.univ) δ (Finset.mem_univ pivot)
  have hb := mul_le_mul_of_nonneg_right hbudget hH
  nlinarith

/-- A fixed integer replication count exists uniformly for positive surplus. -/
theorem exists_replication_count {c C : ℝ} (hc : 0 < c) :
    ∃ r : ℕ, 1 ≤ r ∧ C ≤ ((r : ℝ) - 1) * c := by
  obtain ⟨k, hk⟩ := exists_nat_ge (C / c)
  refine ⟨k + 1, by omega, ?_⟩
  have h := (div_le_iff₀ hc).mp hk
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h

/-- Extra variance is harmless when a group is deleted or retained. -/
lemma replication_variance_deficit {M V : ℝ} (hM : 1 ≤ M) (hV : 0 ≤ V) :
    0 ≤ M ^ 2 * V ∧ 0 ≤ (M ^ 2 - 1) * V := by
  constructor
  · positivity
  · exact mul_nonneg (by nlinarith) hV

end ProofProject
