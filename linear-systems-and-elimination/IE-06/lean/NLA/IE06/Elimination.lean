import NLA.IE06.Definitions
import Mathlib

/-! Exact left elimination operators. Preimplementation independent review is
recorded in `reviews/elimination-specification.md`. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.IE06

/-- Left row operation, retaining all original input coordinates. -/
def eliminationStep {n : ℕ} (S E : Mat n) (k p : Fin n) : Mat n :=
  let B := rowSwap S k p
  let R := rowSwap E k p
  fun i j => if k < i then R i j - (B i k / B k k) * R k j else 0

def eliminationRows {n : ℕ} (A : Mat n) (path : PivotPath n) : ℕ → Mat n
  | 0 => (1 : Matrix (Fin n) (Fin n) ℝ)
  | k + 1 => if h : k < n then
      eliminationStep (trajectory A path k) (eliminationRows A path k)
        ⟨k,h⟩ (path ⟨k,h⟩) else 0

theorem eliminationStep_mul {n : ℕ} (A S E : Mat n) (k p i j : Fin n)
    (hj : k < j) (hjE : ∀ a, (Matrix.of E * Matrix.of A) a j = S a j) :
    (Matrix.of (eliminationStep S E k p) * Matrix.of A) i j = schurStep S k p i j := by
  classical
  by_cases hi : k < i
  · simp only [Matrix.mul_apply, Matrix.of_apply, eliminationStep, hi, ↓reduceIte,
      sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change (Matrix.of E * Matrix.of A) (Equiv.swap k p i) j -
      (rowSwap S k p i k / rowSwap S k p k k) *
        (Matrix.of E * Matrix.of A) (Equiv.swap k p k) j = _
    rw [hjE, hjE]
    simp only [schurStep, hi, hj, and_self, ↓reduceIte, rowSwap]
  · simp [Matrix.mul_apply, eliminationStep, schurStep, hi]

/-- Every still-active column is exactly obtained by the left operator. -/
theorem eliminationRows_mul {n : ℕ} (A : Mat n) (path : PivotPath n)
    (k : ℕ) (i j : Fin n) (hj : k ≤ j.val) :
    (Matrix.of (eliminationRows A path k) * Matrix.of A) i j = trajectory A path k i j := by
  induction k generalizing i j with
  | zero =>
      change ((1 : Matrix (Fin n) (Fin n) ℝ) * Matrix.of A) i j = A i j
      rw [Matrix.one_mul]
      rfl
  | succ k ih =>
      have hk : k < n := lt_of_lt_of_le (by omega : k < j.val+1) (Nat.succ_le_of_lt j.isLt)
      simp only [eliminationRows, trajectory, dif_pos hk]
      apply eliminationStep_mul
      · exact show k < j.val by omega
      · intro a
        exact ih a j (by omega)

/-- Rows already eliminated are zero, even for totalized invalid paths. -/
theorem eliminationRows_inactive {n : ℕ} (A : Mat n) (path : PivotPath n)
    {k : ℕ} (i j : Fin n) (hi : i.val < k) : eliminationRows A path k i j = 0 := by
  cases k with
  | zero => omega
  | succ k =>
      by_cases hk : k < n
      · rw [eliminationRows, dif_pos hk]
        simp only [eliminationStep]
        exact if_neg (by change ¬ k < i.val; omega)
      · simp [eliminationRows, hk]

theorem eliminationRows_terminal {n : ℕ} (A : Mat n) (path : PivotPath n) :
    eliminationRows A path n = 0 := by
  funext i j
  exact eliminationRows_inactive A path i j i.isLt

def rowL1 {n : ℕ} (E : Mat n) (i : Fin n) : ℝ := ∑ j, |E i j|

private theorem swap_active_elimination {n : ℕ} (k p i : Fin n)
    (hp : k ≤ p) (hi : k ≤ i) : k ≤ Equiv.swap k p i := by
  by_cases hik : i = k
  · subst i; simpa using hp
  by_cases hip : i = p
  · subst i; simp
  simpa [Equiv.swap_apply_of_ne_of_ne hik hip] using hi

theorem admissible_multiplier_le_one {n : ℕ} (S : Mat n) (k p i : Fin n)
    (hp : AdmissiblePivot S k p) (hi : k ≤ i) :
    |rowSwap S k p i k / rowSwap S k p k k| ≤ 1 := by
  have hmax := hp.2.2 (Equiv.swap k p i) (swap_active_elimination k p i hp.1 hi)
  have hnz : 0 < |S p k| := abs_pos.mpr hp.2.1
  simpa only [rowSwap, Equiv.swap_apply_left, abs_div] using (div_le_one hnz).2 hmax

theorem eliminationStep_rowL1_le {n : ℕ} (S E : Mat n) (k p i : Fin n)
    (M : ℝ) (hM : 0 ≤ M) (hE : ∀ a, rowL1 E a ≤ M)
    (hp : AdmissiblePivot S k p) : rowL1 (eliminationStep S E k p) i ≤ 2*M := by
  classical
  by_cases hi : k < i
  · have hc := admissible_multiplier_le_one S k p i hp hi.le
    calc
      rowL1 (eliminationStep S E k p) i ≤
          rowL1 E (Equiv.swap k p i) +
          |rowSwap S k p i k / rowSwap S k p k k| * rowL1 E (Equiv.swap k p k) := by
        simp only [rowL1, eliminationStep, hi, ↓reduceIte, Finset.mul_sum,
          ← Finset.sum_add_distrib, rowSwap]
        apply Finset.sum_le_sum
        intro j _
        simpa only [abs_mul] using abs_sub (E (Equiv.swap k p i) j)
          ((S (Equiv.swap k p i) k / S (Equiv.swap k p k) k) * E (Equiv.swap k p k) j)
      _ ≤ M + 1*M := add_le_add (hE _) (mul_le_mul hc (hE _) (by unfold rowL1; positivity) (by norm_num))
      _ = 2*M := by ring
  · simp only [rowL1, eliminationStep, hi, ↓reduceIte, abs_zero, Finset.sum_const_zero]
    positivity

theorem eliminationRows_rowL1_le {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hp : AdmissiblePath A path) (k : ℕ) (i : Fin n) :
    rowL1 (eliminationRows A path k) i ≤ (2 : ℝ)^k := by
  induction k generalizing i with
  | zero => simp [eliminationRows, rowL1, Matrix.one_apply, apply_ite, abs_one, abs_zero]
  | succ k ih =>
      by_cases hk : k < n
      · simp only [eliminationRows, dif_pos hk]
        calc
          rowL1 (eliminationStep (trajectory A path k) (eliminationRows A path k)
            ⟨k,hk⟩ (path ⟨k,hk⟩)) i ≤ 2*(2:ℝ)^k :=
              eliminationStep_rowL1_le _ _ _ _ _ _ (by positivity)
                ih (hp ⟨k,hk⟩)
          _ = (2:ℝ)^(k+1) := by ring
      · simp [eliminationRows, hk, rowL1]

/-- Agreement of the first d original columns. -/
def ColumnsAgree {n : ℕ} (A B : Mat n) (d : ℕ) : Prop :=
  ∀ i j, j.val < d → A i j = B i j

/-- Fixed-path Schur entries in the first d columns use only those columns
while at most d eliminations have been completed. -/
theorem trajectory_columns_congr {n : ℕ} (A B : Mat n) (path : PivotPath n)
    (d : ℕ) (hAB : ColumnsAgree A B d) (k : ℕ) (hk : k ≤ d) :
    ColumnsAgree (trajectory A path k) (trajectory B path k) d := by
  induction k with
  | zero => exact hAB
  | succ k ih =>
      have hprev := ih (by omega)
      intro i j hj
      by_cases hkn : k < n
      · rw [trajectory, trajectory, dif_pos hkn, dif_pos hkn]
        simp only [schurStep, rowSwap]
        split_ifs with h
        · rw [hprev _ j hj, hprev _ ⟨k,hkn⟩ (by omega),
            hprev _ ⟨k,hkn⟩ (by omega), hprev _ j hj]
        · rfl
      · simp only [trajectory, dif_neg hkn]

theorem eliminationRows_columns_congr {n : ℕ} (A B : Mat n) (path : PivotPath n)
    (d : ℕ) (hAB : ColumnsAgree A B d) (k : ℕ) (hk : k ≤ d) :
    eliminationRows A path k = eliminationRows B path k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hprev := ih (by omega)
      by_cases hkn : k < n
      · rw [eliminationRows, eliminationRows, dif_pos hkn, dif_pos hkn, hprev]
        have hc := trajectory_columns_congr A B path d hAB k (by omega)
        funext i j
        simp only [eliminationStep, rowSwap]
        rw [hc _ ⟨k,hkn⟩ (by change k < d; omega), hc _ ⟨k,hkn⟩ (by change k < d; omega)]
      · simp only [eliminationRows, dif_neg hkn]

/-- Only the first k original columns determine a fixed-path left operator
at stage k. This statement does not assume a data-dependent path is fixed. -/
theorem eliminationRows_depends_on_prefix {n : ℕ} (A B : Mat n)
    (path : PivotPath n) (k : ℕ) (hAB : ColumnsAgree A B k) :
    eliminationRows A path k = eliminationRows B path k :=
  eliminationRows_columns_congr A B path k hAB k le_rfl

#assert_trust kernel trajectory_columns_congr
#assert_trust kernel eliminationRows_columns_congr
#assert_trust kernel eliminationRows_depends_on_prefix
#print axioms trajectory_columns_congr
#print axioms eliminationRows_columns_congr
#print axioms eliminationRows_depends_on_prefix
#assert_trust kernel eliminationRows_mul
#assert_trust kernel eliminationRows_inactive
#assert_trust kernel eliminationRows_terminal
#assert_trust kernel admissible_multiplier_le_one
#assert_trust kernel eliminationStep_rowL1_le
#assert_trust kernel eliminationRows_rowL1_le
#print axioms eliminationRows_mul
#print axioms eliminationRows_inactive
#print axioms eliminationRows_terminal
#print axioms admissible_multiplier_le_one
#print axioms eliminationStep_rowL1_le
#print axioms eliminationRows_rowL1_le
end NLA.IE06
