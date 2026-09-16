import NLA.IE05.Definitions
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.FinRange
import Mathlib.Tactic
import LeanCert.Tactic.Verification

/-!
# Exact first-available partial-pivot selection

The frozen scan is related to Mathlib's actual first-occurring `List.argmax`.
No nonsingularity or candidate-specific hypothesis is needed for the scan's
maximality/minimal-index property or for uniqueness of an already valid path.
Implementation: formal_review_standards AI agent for George Stepaniants.
-/

noncomputable section
open scoped BigOperators
namespace NLA.IE05

private def pivotScore {n : ℕ} (S : Mat n) (k i : Fin n) : ℝ :=
  if k ≤ i then |S i k| else -1

private def pivotUpdate {n : ℕ} (S : Mat n) (k p i : Fin n) : Fin n :=
  if k ≤ i ∧ |S p k| < |S i k| then i else p

private theorem pivotUpdate_active {n : ℕ} (S : Mat n) (k p i : Fin n)
    (hp : k ≤ p) : k ≤ pivotUpdate S k p i := by
  unfold pivotUpdate
  split_ifs with h
  · exact h.1
  · exact hp

private theorem pivotFold_active {n : ℕ} (S : Mat n) (k : Fin n)
    (l : List (Fin n)) (p : Fin n) (hp : k ≤ p) :
    k ≤ l.foldl (pivotUpdate S k) p := by
  induction l generalizing p with
  | nil => exact hp
  | cons i l ih => exact ih _ (pivotUpdate_active S k p i hp)

private theorem pivotScore_lt_iff {n : ℕ} (S : Mat n) (k p i : Fin n)
    (hp : k ≤ p) :
    pivotScore S k p < pivotScore S k i ↔ k ≤ i ∧ |S p k| < |S i k| := by
  by_cases hi : k ≤ i
  · simp [pivotScore, hp, hi]
  · have hnot : ¬ |S p k| < -1 := by have := abs_nonneg (S p k); linarith
    simp [pivotScore, hp, hi, hnot]

private theorem pivotFold_argAux {n : ℕ} (S : Mat n) (k : Fin n)
    (l : List (Fin n)) (p : Fin n) (hp : k ≤ p) :
    l.foldl (List.argAux (fun i r => pivotScore S k r < pivotScore S k i)) (some p) =
      some (l.foldl (pivotUpdate S k) p) := by
  induction l generalizing p with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons, List.argAux]
    by_cases h : k ≤ i ∧ |S p k| < |S i k|
    · have hs := (pivotScore_lt_iff S k p i hp).2 h
      simp only [if_pos hs, pivotUpdate, if_pos h]
      exact ih i h.1
    · have hs : ¬ pivotScore S k p < pivotScore S k i :=
        fun hs => h ((pivotScore_lt_iff S k p i hp).1 hs)
      simp only [if_neg hs, pivotUpdate, if_neg h]
      exact ih p hp

/-- The actual scan is active, maximizes column magnitude and chooses the least
current row among ties, even when the whole active column is zero. -/
theorem firstPivotIndex_spec_proved {n : ℕ} (S : Mat n) (k : Fin n) :
    k ≤ firstPivotIndex S k ∧
      (∀ i, k ≤ i → |S i k| ≤ |S (firstPivotIndex S k) k|) ∧
      ∀ i, k ≤ i → |S i k| = |S (firstPivotIndex S k) k| → firstPivotIndex S k ≤ i := by
  let r := firstPivotIndex S k
  have hr : k ≤ r := pivotFold_active S k (List.finRange n) k le_rfl
  have hm : r ∈ List.argmax (pivotScore S k) (k :: List.finRange n) := by
    unfold List.argmax
    simp only [List.foldl_cons, List.argAux]
    rw [pivotFold_argAux S k (List.finRange n) k le_rfl]
    exact Option.mem_def.mpr rfl
  refine ⟨hr, ?_, ?_⟩
  · intro i hi
    have h := List.le_of_mem_argmax (List.mem_cons_of_mem k (List.mem_finRange i)) hm
    simpa [pivotScore, hi, hr] using h
  · intro i hi heq
    have hscore : pivotScore S k r ≤ pivotScore S k i := by
      simpa [pivotScore, hi, hr] using heq.ge
    have hind := List.index_of_argmax hm (List.mem_cons_of_mem k (List.mem_finRange i)) hscore
    change r ≤ i
    by_cases hrk : r = k
    · simpa only [hrk] using hi
    · by_cases hik : i = k
      · rw [List.idxOf_cons_ne _ (Ne.symm hrk), hik, List.idxOf_cons_self] at hind
        omega
      · rw [List.idxOf_cons_ne _ (Ne.symm hrk), List.idxOf_cons_ne _ (Ne.symm hik),
            List.idxOf_finRange, List.idxOf_finRange] at hind
        exact Nat.le_of_succ_le_succ hind

/-- Any row satisfying the independent first-available specification is the scan result. -/
theorem firstPivotIndex_eq_of_firstAvailable_proved {n : ℕ} (S : Mat n)
    (k p : Fin n) (hp : FirstAvailablePivot S k p) : firstPivotIndex S k = p := by
  obtain ⟨hr, hmax, hmin⟩ := firstPivotIndex_spec_proved S k
  have heq : |S p k| = |S (firstPivotIndex S k) k| :=
    le_antisymm (hmax p hp.1.1) (hp.1.2.2 _ hr)
  exact le_antisymm (hmin p hp.1.1 heq) (hp.2 _ hr heq.symm)

/-- A nonzero active column makes the scan an admissible first-available pivot. -/
theorem firstPivotIndex_firstAvailable_proved {n : ℕ} (S : Mat n) (k : Fin n)
    (hex : ∃ i, k ≤ i ∧ S i k ≠ 0) :
    FirstAvailablePivot S k (firstPivotIndex S k) := by
  obtain ⟨hr, hmax, hmin⟩ := firstPivotIndex_spec_proved S k
  refine ⟨⟨hr, ?_, hmax⟩, hmin⟩
  intro hz
  obtain ⟨i, hi, hne⟩ := hex
  have h := hmax i hi
  rw [hz, abs_zero] at h
  exact hne (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- The two actual recursive trajectories agree for the explicitly defined scan path. -/
theorem trajectory_firstPath_eq_proved {n : ℕ} (A : Mat n) (k : ℕ) :
    trajectory A (firstPath A) k = firstTrajectory A k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < n
    · simp [trajectory, firstTrajectory, firstPath, hk, ih]
    · simp [trajectory, firstTrajectory, hk]

/-- Already valid first-available paths are uniquely determined. This theorem
does not assume determinant nonzero, so LU-based clients can use it directly. -/
theorem firstPath_eq_of_firstAvailable_proved {n : ℕ} (A : Mat n)
    (path : PivotPath n) (hp : FirstAvailablePath A path) : path = firstPath A := by
  have hstates : ∀ k, trajectory A path k = firstTrajectory A k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      by_cases hk : k < n
      · have hs : FirstAvailablePivot (firstTrajectory A k) ⟨k, hk⟩ (path ⟨k, hk⟩) := by
          simpa [ih] using hp ⟨k, hk⟩
        have he := firstPivotIndex_eq_of_firstAvailable_proved _ _ _ hs
        simp [trajectory, firstTrajectory, hk, ih, he]
      · simp [trajectory, firstTrajectory, hk]
  funext k
  have he := firstPivotIndex_eq_of_firstAvailable_proved _ _ _ (hp k)
  simpa [hstates, firstPath] using he.symm

#assert_trust kernel firstPivotIndex_spec_proved
#print axioms firstPivotIndex_spec_proved
#assert_trust kernel firstPivotIndex_eq_of_firstAvailable_proved
#print axioms firstPivotIndex_eq_of_firstAvailable_proved
#assert_trust kernel firstPivotIndex_firstAvailable_proved
#print axioms firstPivotIndex_firstAvailable_proved
#assert_trust kernel trajectory_firstPath_eq_proved
#print axioms trajectory_firstPath_eq_proved
#assert_trust kernel firstPath_eq_of_firstAvailable_proved
#print axioms firstPath_eq_of_firstAvailable_proved

end NLA.IE05
