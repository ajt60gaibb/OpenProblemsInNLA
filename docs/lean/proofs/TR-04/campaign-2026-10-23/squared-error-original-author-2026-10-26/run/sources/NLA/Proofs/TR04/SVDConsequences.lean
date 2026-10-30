import NLA.Proofs.TR04.SVDEckartThreshold

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

theorem tailEnergy_eq_zero_iff {p : ℕ} (sigma : Fin p → ℝ) (r : ℕ) :
    tailEnergy sigma r = 0 ↔ ∀ k, r ≤ k.val → sigma k = 0 := by
  constructor
  · intro h k hk
    have hnon (i : Fin p) : 0 ≤ (if r ≤ i.val then (sigma i)^2 else 0) := by
      split_ifs <;> positivity
    have hle := Finset.single_le_sum (fun i _ => hnon i) (Finset.mem_univ k)
    change (if r ≤ k.val then (sigma k)^2 else 0) ≤ tailEnergy sigma r at hle
    rw [if_pos hk, h] at hle
    nlinarith [sq_nonneg (sigma k)]
  · intro h
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : r ≤ k.val
    · simp [hk, h k hk]
    · simp [hk]

theorem validSVD_rank_le_iff_tail_zero {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) :
    Matrix.rank B ≤ r ↔ tailEnergy sigma r = 0 := by
  constructor
  · intro hr
    have hle := validSVD_eckartYoung h r B hr
    have hz : matrixEnergy (B - B) = 0 := by simp [matrixEnergy]
    rw [hz] at hle
    exact le_antisymm hle (tailEnergy_nonneg sigma r)
  · intro hz
    have hb := (validSVD_zero_tail_iff_truncate h r).mp hz
    rw [← hb]
    exact truncate_rank_le U sigma V r

theorem validSVD_truncate_best {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) :
    Matrix.rank (truncate U sigma V r) ≤ r ∧
      ∀ Y, Matrix.rank Y ≤ r → matrixEnergy (B - truncate U sigma V r) ≤
        matrixEnergy (B - Y) := by
  refine ⟨truncate_rank_le U sigma V r, ?_⟩
  intro Y hY
  rw [validSVD_truncate_error h]
  exact validSVD_eckartYoung h r Y hY

theorem validSVD_positive_tail {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ)
    (ht : 0 < tailEnergy sigma r) :
    ∃ hr : r < min m l, 0 < sigma ⟨r, hr⟩ := by
  have hr : r < min m l := by
    by_contra hn
    rw [tailEnergy_eq_zero_of_length_le sigma (Nat.le_of_not_gt hn)] at ht
    exact (lt_irrefl 0) ht
  refine ⟨hr, ?_⟩
  by_contra hn
  have hs0 : sigma ⟨r, hr⟩ = 0 :=
    le_antisymm (le_of_not_gt hn) (h.2.2.1 _)
  have hz : tailEnergy sigma r = 0 := (tailEnergy_eq_zero_iff sigma r).mpr (by
    intro k hk
    have hle := h.2.2.2.1 ⟨r, hr⟩ k (Fin.le_iff_val_le_val.mpr hk)
    rw [hs0] at hle
    exact le_antisymm hle (h.2.2.1 k))
  rw [hz] at ht
  exact (lt_irrefl 0) ht

#assert_trust kernel validSVD_rank_le_iff_tail_zero
#assert_trust kernel validSVD_truncate_best
#assert_trust kernel validSVD_positive_tail
#print axioms validSVD_truncate_best
end NLA.Proofs.TR04.SVD
