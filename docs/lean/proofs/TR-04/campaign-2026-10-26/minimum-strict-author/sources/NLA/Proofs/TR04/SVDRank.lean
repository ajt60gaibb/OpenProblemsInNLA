import NLA.Proofs.TR04.SVDEnergy

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

/-- The finite truncated sum factors through at most the requested number of
columns. This is an actual real matrix rank bound and needs no SVD hypotheses. -/
theorem truncate_rank_le {m l : ℕ}
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (r : ℕ) :
    Matrix.rank (truncate U sigma V r) ≤ r := by
  classical
  let q := min r (min m l)
  have hqp : q ≤ min m l := Nat.min_le_right _ _
  let c : Fin q → Fin (min m l) := Fin.castLE hqp
  let L : Matrix (Fin m) (Fin q) ℝ := fun i k =>
    U i (Fin.castLE (Nat.min_le_left m l) (c k)) * sigma (c k)
  let R : Matrix (Fin q) (Fin l) ℝ := fun k j =>
    V j (Fin.castLE (Nat.min_le_right m l) (c k))
  have hfac : truncate U sigma V r = L * R := by
    ext i j
    change (∑ k : Fin (min m l),
      U i (Fin.castLE (Nat.min_le_left m l) k) *
        (if k.val < r then sigma k else 0) *
        V j (Fin.castLE (Nat.min_le_right m l) k)) = _
    rw [sum_fin_truncate hqp]
    · apply Finset.sum_congr rfl
      intro k _
      have hk : (Fin.castLE hqp k).val < r :=
        lt_of_lt_of_le k.isLt (Nat.min_le_left r (min m l))
      simp only [L, R, c, if_pos hk]
    · intro k hk
      have hkr : ¬ k.val < r := by
        dsimp [q] at hk
        omega
      simp only [if_neg hkr, mul_zero, zero_mul]
  rw [hfac]
  exact (Matrix.rank_mul_le_left L R).trans
    ((Matrix.rank_le_card_width L).trans (by simp [q]))

theorem matrixEnergy_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ) : 0 ≤ matrixEnergy M := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem matrixEnergy_entry_sq_le {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ) (i : α) (j : β) : (M i j)^2 ≤ matrixEnergy M := by
  classical
  exact (Finset.single_le_sum (fun k _ => sq_nonneg (M i k)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg (M a b))
      (Finset.mem_univ i))

theorem matrixEnergy_eq_zero_iff {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ) : matrixEnergy M = 0 ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    change M i j = 0
    have hle := matrixEnergy_entry_sq_le M i j
    rw [h] at hle
    have hz : (M i j)^2 = 0 := le_antisymm hle (sq_nonneg _)
    nlinarith [sq_nonneg (M i j)]
  · rintro rfl
    simp [matrixEnergy]

theorem matrixError_eq_zero_iff {α β : Type*} [Fintype α] [Fintype β]
    (A B : Matrix α β ℝ) : matrixEnergy (A - B) = 0 ↔ A = B := by
  rw [matrixEnergy_eq_zero_iff, sub_eq_zero]

theorem validSVD_zero_tail_iff_truncate {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) :
    tailEnergy sigma r = 0 ↔ truncate U sigma V r = B := by
  rw [← validSVD_truncate_error h, matrixError_eq_zero_iff, eq_comm]

theorem tailEnergy_nonneg {p : ℕ} (sigma : Fin p → ℝ) (r : ℕ) :
    0 ≤ tailEnergy sigma r := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

#assert_trust kernel truncate_rank_le
#assert_trust kernel matrixEnergy_eq_zero_iff
#assert_trust kernel validSVD_zero_tail_iff_truncate
#print axioms truncate_rank_le

end NLA.Proofs.TR04.SVD
