import NLA.Proofs.RE06.SVDPartition

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.RE06.Repair

def tailIndex (n d : ℕ) (hd : d ≤ n) (j : Fin (n-d)) : Fin n :=
  ⟨d+j.val,by omega⟩

def tailEmbedding (n d : ℕ) (hd : d ≤ n) : Matrix (Fin n) (Fin (n-d)) ℝ :=
  fun i j => if i=tailIndex n d hd j then 1 else 0

theorem tailIndex_injective (n d : ℕ) (hd : d ≤ n) :
    Function.Injective (tailIndex n d hd) := by
  intro i j h
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val h)

theorem tailEmbedding_gram (n d : ℕ) (hd : d ≤ n) :
    (tailEmbedding n d hd).transpose*tailEmbedding n d hd=1 := by
  ext i j
  simp [tailEmbedding, Matrix.mul_apply, Matrix.one_apply, tailIndex_injective n d hd |>.eq_iff,
    eq_comm]

theorem tailEmbedding_projector (n d : ℕ) (hd : d ≤ n) :
    tailEmbedding n d hd*(tailEmbedding n d hd).transpose =
      Matrix.diagonal (fun i : Fin n => if d ≤ i.val then (1:ℝ) else 0) := by
  ext i j
  by_cases hi : d ≤ i.val
  · let ii : Fin (n-d) := ⟨i.val-d,by omega⟩
    have he : tailIndex n d hd ii=i := by
      apply Fin.ext
      exact Nat.add_sub_of_le hi
    rw [Matrix.mul_apply, Finset.sum_eq_single ii]
    · simp [tailEmbedding, he, Matrix.diagonal_apply, hi, eq_comm]
    · intro b _ hb
      have hne : i ≠ tailIndex n d hd b := by
        intro h
        apply hb
        exact tailIndex_injective n d hd (h.symm.trans he.symm)
      simp [tailEmbedding, hne]
    · intro h
      exact (h (Finset.mem_univ ii)).elim
  · have hne : ∀ b : Fin (n-d), i ≠ tailIndex n d hd b := by
      intro b h
      have hh := congrArg Fin.val h
      change i.val=d+b.val at hh
      omega
    simp [Matrix.mul_apply, tailEmbedding, hne, Matrix.diagonal_apply, hi]

theorem head_tail_projectors (n d : ℕ) (hd : d ≤ n) :
    headEmbedding n d hd*(headEmbedding n d hd).transpose +
      tailEmbedding n d hd*(tailEmbedding n d hd).transpose=1 := by
  rw [headEmbedding_projector, tailEmbedding_projector]
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    by_cases h : i.val < d
    · simp [h, Nat.not_le.mpr h]
    · simp [h, Nat.le_of_not_lt h]
  · simp [Matrix.add_apply, hij]

#assert_trust kernel tailIndex_injective
#assert_trust kernel tailEmbedding_gram
#assert_trust kernel tailEmbedding_projector
#assert_trust kernel head_tail_projectors
#print axioms head_tail_projectors
end NLA.Proofs.RE06.Repair
