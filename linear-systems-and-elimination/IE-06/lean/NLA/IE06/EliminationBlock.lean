import NLA.IE06.Elimination

/-! Actual left elimination operators over a block of stages. The exact
contract was independently reviewed before implementation; see
reviews/elimination-block-specification.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace NLA.IE06

/-- The real row operations at absolute stages t,...,t+s-1, starting from I. -/
def blockRows {n : ℕ} (A : Mat n) (path : PivotPath n) (t : ℕ) : ℕ → Mat n
  | 0 => (1 : Matrix (Fin n) (Fin n) ℝ)
  | s + 1 => if h : t + s < n then
      eliminationStep (trajectory A path (t+s)) (blockRows A path t s)
        ⟨t+s,h⟩ (path ⟨t+s,h⟩) else 0

theorem eliminationStep_mul_apply {n : ℕ} (S E A : Mat n) (k p i j : Fin n) :
    (Matrix.of (eliminationStep S E k p) * Matrix.of A) i j =
      if k < i then
        (Matrix.of E * Matrix.of A) (Equiv.swap k p i) j -
          (rowSwap S k p i k / rowSwap S k p k k) *
            (Matrix.of E * Matrix.of A) (Equiv.swap k p k) j
      else 0 := by
  classical
  by_cases hi : k < i
  · simp only [Matrix.mul_apply, Matrix.of_apply, eliminationStep, hi, ↓reduceIte,
      sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, rowSwap]
  · simp [Matrix.mul_apply, eliminationStep, hi]

theorem eliminationStep_right_mul {n : ℕ} (S E F : Mat n) (k p : Fin n) :
    Matrix.of (eliminationStep S E k p) * Matrix.of F =
      Matrix.of (eliminationStep S (Matrix.of E * Matrix.of F) k p) := by
  ext i j
  rw [eliminationStep_mul_apply]
  rfl

theorem blockRows_mul {n : ℕ} (A : Mat n) (path : PivotPath n) (t s : ℕ) :
    Matrix.of (blockRows A path t s) * Matrix.of (eliminationRows A path t) =
      Matrix.of (eliminationRows A path (t+s)) := by
  induction s with
  | zero =>
      change (1 : Matrix (Fin n) (Fin n) ℝ) * Matrix.of (eliminationRows A path t) = _
      simp
  | succ s ih =>
      by_cases h : t+s < n
      · rw [blockRows, dif_pos h, Nat.add_succ, eliminationRows, dif_pos h,
          eliminationStep_right_mul, ih]
        rfl
      · rw [blockRows, dif_neg h, Nat.add_succ, eliminationRows, dif_neg h]
        exact Matrix.zero_mul _

theorem blockRows_rowL1_le {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hp : AdmissiblePath A path) (t s : ℕ) (i : Fin n) :
    rowL1 (blockRows A path t s) i ≤ (2 : ℝ)^s := by
  induction s generalizing i with
  | zero => simp [blockRows, rowL1, Matrix.one_apply, apply_ite, abs_one, abs_zero]
  | succ s ih =>
      by_cases h : t+s < n
      · rw [blockRows, dif_pos h]
        calc
          _ ≤ 2 * (2:ℝ)^s := eliminationStep_rowL1_le _ _ _ _ _ _
            (by positivity) ih (hp ⟨t+s,h⟩)
          _ = (2:ℝ)^(s+1) := by ring
      · simp [blockRows, h, rowL1]

/-- Already processed original columns are annihilated by the exact left operator. -/
theorem eliminationRows_annihilates {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hp : AdmissiblePath A path) (k : ℕ) (i j : Fin n) (hj : j.val < k) :
    (Matrix.of (eliminationRows A path k) * Matrix.of A) i j = 0 := by
  induction k generalizing i j with
  | zero => omega
  | succ k ih =>
      by_cases hk : k < n
      · rw [eliminationRows, dif_pos hk, eliminationStep_mul_apply]
        split_ifs with hi
        · by_cases hjk : j.val < k
          · rw [ih _ j hjk, ih _ j hjk]
            ring
          · have heq : j = ⟨k,hk⟩ := Fin.ext (by change j.val = k; omega)
            subst j
            rw [eliminationRows_mul A path k _ _ le_rfl,
              eliminationRows_mul A path k _ _ le_rfl]
            have hnz := (hp ⟨k,hk⟩).2.1
            simp only [rowSwap, Equiv.swap_apply_left]
            rw [div_mul_cancel₀ _ hnz, sub_self]
        · rfl
      · rw [eliminationRows, dif_neg hk]
        exact congrFun (congrFun (Matrix.zero_mul (Matrix.of A)) i) j

/-- The next s columns of the original input, in their original order. -/
def blockColumns {n : ℕ} (A : Mat n) (t s : ℕ) (h : t+s ≤ n) :
    Matrix (Fin n) (Fin s) ℝ :=
  fun i j => A i ⟨t+j.val, by omega⟩

theorem blockRows_annihilates_block {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hp : AdmissiblePath A path) (t s : ℕ) (h : t+s ≤ n) :
    (Matrix.of (blockRows A path t s) * Matrix.of (eliminationRows A path t)) *
      blockColumns A t s h = 0 := by
  rw [blockRows_mul]
  ext i j
  change (Matrix.of (eliminationRows A path (t+s)) * Matrix.of A) i
    ⟨t+j.val, by omega⟩ = 0
  exact eliminationRows_annihilates A path hp (t+s) i _ (by dsimp; omega)

#assert_trust kernel blockRows
#assert_trust kernel eliminationStep_mul_apply
#assert_trust kernel eliminationStep_right_mul
#assert_trust kernel blockRows_mul
#assert_trust kernel blockRows_rowL1_le
#assert_trust kernel eliminationRows_annihilates
#assert_trust kernel blockColumns
#assert_trust kernel blockRows_annihilates_block
#print axioms blockRows_mul
#print axioms blockRows_rowL1_le
#print axioms eliminationRows_annihilates
#print axioms blockRows_annihilates_block
end NLA.IE06
