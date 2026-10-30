import NLA.Proofs.TR04.SVDProjectionRank

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Matrix BigOperators
namespace NLA.Proofs.TR04.SVD

def selectedFrame {m l : ℕ} (U : Matrix (Fin m) (Fin m) ℝ)
    (P : Fin (min m l) → Prop) : Matrix (Fin m) {k // P k} ℝ :=
  fun i k => U i (Fin.castLE (Nat.min_le_left m l) k.val)

theorem orthonormalColumns_selectedFrame {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (P : Fin (min m l) → Prop) : OrthonormalColumns (selectedFrame U P) := by
  classical
  exact orthonormalColumns_submatrix hU _ (by
    intro i j hij
    apply Subtype.ext
    exact Fin.ext (congrArg (fun k : Fin m => k.val) hij))

theorem orthonormalColumns_rank {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    {Q : Matrix α β ℝ} (hQ : OrthonormalColumns Q) : Matrix.rank Q = Fintype.card β := by
  have h1 : Matrix.rank (Q.transpose * Q) = Fintype.card β := by
    rw [transpose_mul_eq_one hQ]
    simp
  have hle := Matrix.rank_mul_le_right Q.transpose Q
  rw [h1] at hle
  exact le_antisymm (Matrix.rank_le_card_width Q) hle

theorem rank_selectedFrame {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (P : Fin (min m l) → Prop) [DecidablePred P] :
    Matrix.rank (selectedFrame U P) = Fintype.card {k // P k} :=
  orthonormalColumns_rank (orthonormalColumns_selectedFrame hU P)

#assert_trust kernel orthonormalColumns_selectedFrame
#assert_trust kernel rank_selectedFrame
#print axioms rank_selectedFrame
end NLA.Proofs.TR04.SVD
