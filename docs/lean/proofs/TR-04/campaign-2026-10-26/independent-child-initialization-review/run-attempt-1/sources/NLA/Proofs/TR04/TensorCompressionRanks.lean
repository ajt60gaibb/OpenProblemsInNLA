import NLA.Proofs.TR04.TensorCompression

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.TensorFormat

/-- The row action at a later cut is the actual first-mode matrix tensored
with the identity on the remaining prefix entries. -/
def prefixAction {m k : ℕ} (M : Matrix (Fin k) (Fin m) ℝ) (pre : List ℕ) :
    Matrix (Index (k :: pre)) (Index (m :: pre)) ℝ := by
  classical
  exact fun x y => if x.2 = y.2 then M x.1 y.1 else 0

theorem unfold_actFirst_succ {m k : ℕ} {ns : List ℕ}
    (M : Matrix (Fin k) (Fin m) ℝ) (A : Tensor (m :: ns)) (j : ℕ) :
    unfold (k :: ns) (actFirst M A) (j + 1) =
      prefixAction M (ns.take j) *
        (show Matrix (Index (m :: ns.take j)) (Index (ns.drop j)) ℝ from
          unfold (m :: ns) A (j + 1)) := by
  classical
  ext x y
  change (∑ i : Fin m, M x.1 i * A (i, joinIndex ns j x.2 y)) = _
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, prefixAction, unfold, joinIndex]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem rank_unfold_actFirst_le {m k : ℕ} {ns : List ℕ}
    (M : Matrix (Fin k) (Fin m) ℝ) (A : Tensor (m :: ns)) (j : ℕ) :
    Matrix.rank (unfold (k :: ns) (actFirst M A) (j + 1)) ≤
      Matrix.rank (unfold (m :: ns) A (j + 1)) := by
  rw [unfold_actFirst_succ]
  exact Matrix.rank_mul_le_right _ _

/-- First-mode contraction preserves every original nontrivial cut bound. -/
theorem rank_unfold_contract_le {m k : ℕ} {ns : List ℕ}
    (U : Matrix (Fin m) (Fin k) ℝ) (A : Tensor (m :: ns)) (j : ℕ) :
    Matrix.rank (unfold (k :: ns) (contract U A) (j + 1)) ≤
      Matrix.rank (unfold (m :: ns) A (j + 1)) :=
  rank_unfold_actFirst_le U.transpose A j

/-- Lifting also preserves every remaining cut bound. -/
theorem rank_unfold_lift_le {m k : ℕ} {ns : List ℕ}
    (U : Matrix (Fin m) (Fin k) ℝ) (A : Tensor (k :: ns)) (j : ℕ) :
    Matrix.rank (unfold (m :: ns) (lift U A) (j + 1)) ≤
      Matrix.rank (unfold (k :: ns) A (j + 1)) :=
  rank_unfold_actFirst_le U A j

def headIndexEquiv (m : ℕ) : Index [m] ≃ Fin m where
  toFun x := x.1
  invFun i := (i, PUnit.unit)
  left_inv x := by rcases x with ⟨i, x⟩; cases x; rfl
  right_inv _ := rfl

/-- The first cut is exactly the first-mode matrix, up to the empty-prefix unit. -/
theorem unfold_one_eq_submatrix {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    unfold (m :: ns) A 1 = (firstMatrix A).submatrix (headIndexEquiv m) id := by
  ext x y
  change A (x.1, joinIndex ns 0 x.2 y) = A (x.1, y)
  rw [joinIndex_zero]

theorem rank_unfold_one {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    Matrix.rank (unfold (m :: ns) A 1) = Matrix.rank (firstMatrix A) := by
  rw [unfold_one_eq_submatrix]
  exact Matrix.rank_submatrix _ (headIndexEquiv m) (Equiv.refl _)

theorem rank_unfold_lift_one_le {m k : ℕ} {ns : List ℕ}
    (U : Matrix (Fin m) (Fin k) ℝ) (A : Tensor (k :: ns)) :
    Matrix.rank (unfold (m :: ns) (lift U A) 1) ≤ k := by
  rw [rank_unfold_one]
  change Matrix.rank (U * firstMatrix A) ≤ k
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width U)

#assert_trust kernel unfold_actFirst_succ
#assert_trust kernel rank_unfold_actFirst_le
#assert_trust kernel rank_unfold_contract_le
#assert_trust kernel rank_unfold_lift_le
#assert_trust kernel rank_unfold_one
#assert_trust kernel rank_unfold_lift_one_le
#print axioms rank_unfold_contract_le
#print axioms rank_unfold_lift_one_le
end NLA.Proofs.TR04.TensorFormat
