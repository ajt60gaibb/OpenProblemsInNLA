import NLA.Proofs.TR04.SVDConsequences

/-! Exact first-column-frame contractions for every legal SVD response. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix
namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

theorem validSVD_prefix_coefficients {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (q : ℕ) (hq : q ≤ min m l) :
    (U.submatrix id (Fin.castLE (hq.trans (Nat.min_le_left m l)))).transpose * B =
      fun a j => sigma (Fin.castLE hq a) *
        V j (Fin.castLE (Nat.min_le_right m l) (Fin.castLE hq a)) := by
  classical
  let Q := U.submatrix id (Fin.castLE (hq.trans (Nat.min_le_left m l)))
  have hrow (a : Fin q) (k : Fin (min m l)) :
      (∑ i, Q i a * U i (Fin.castLE (Nat.min_le_left m l) k)) =
        if Fin.castLE hq a = k then 1 else 0 := by
    have he : (Fin.castLE (hq.trans (Nat.min_le_left m l)) a =
        Fin.castLE (Nat.min_le_left m l) k) ↔ Fin.castLE hq a = k := by
      constructor <;> intro he
      · exact Fin.ext (congrArg (fun i : Fin m => i.val) he)
      · exact Fin.ext (congrArg (fun i : Fin (min m l) => i.val) he)
    simpa only [Q, Matrix.submatrix_apply, id_eq, he] using
      h.1 (Fin.castLE (hq.trans (Nat.min_le_left m l)) a)
        (Fin.castLE (Nat.min_le_left m l) k)
  ext a j
  change (Q.transpose * B) a j = _
  calc
    (Q.transpose * B) a j = ∑ i, Q i a *
        ∑ k, U i (Fin.castLE (Nat.min_le_left m l) k) * sigma k *
          V j (Fin.castLE (Nat.min_le_right m l) k) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [h.2.2.2.2 i j]
      rfl
    _ = ∑ k, (∑ i, Q i a * U i (Fin.castLE (Nat.min_le_left m l) k)) *
        sigma k * V j (Fin.castLE (Nat.min_le_right m l) k) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = sigma (Fin.castLE hq a) *
        V j (Fin.castLE (Nat.min_le_right m l) (Fin.castLE hq a)) := by
      simp_rw [hrow, ite_mul, one_mul, zero_mul]
      simp

theorem validSVD_prefix_projection {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) :
    let q := min r (min m l)
    let Q := U.submatrix id (Fin.castLE
      ((Nat.min_le_right r (min m l)).trans (Nat.min_le_left m l)))
    Q * (Q.transpose * B) = truncate U sigma V r := by
  classical
  dsimp only
  let q := min r (min m l)
  have hq : q ≤ min m l := Nat.min_le_right _ _
  rw [validSVD_prefix_coefficients h q hq]
  ext i j
  symm
  change (∑ k : Fin (min m l),
    U i (Fin.castLE (Nat.min_le_left m l) k) *
      (if k.val < r then sigma k else 0) *
      V j (Fin.castLE (Nat.min_le_right m l) k)) = _
  rw [sum_fin_truncate hq]
  · apply Finset.sum_congr rfl
    intro k _
    have hk : (Fin.castLE hq k).val < r :=
      lt_of_lt_of_le k.isLt (Nat.min_le_left _ _)
    simp only [if_pos hk, Matrix.submatrix_apply, id_eq]
    have hc : Fin.castLE (Nat.min_le_left m l) (Fin.castLE hq k) =
        Fin.castLE (hq.trans (Nat.min_le_left m l)) k := Fin.ext rfl
    rw [hc]
    ring
  · intro k hk
    have hkr : ¬ k.val < r := by dsimp [q] at hk; omega
    simp only [if_neg hkr, mul_zero, zero_mul]

#assert_trust kernel validSVD_prefix_coefficients
#assert_trust kernel validSVD_prefix_projection
#print axioms validSVD_prefix_projection
end NLA.Proofs.TR04.SVD
