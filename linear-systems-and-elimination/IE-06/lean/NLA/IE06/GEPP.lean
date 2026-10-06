/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The generic GEPP implementation below is adapted from IE-05 at upstream
8f04b905eb2e0827b6b84f37d9d080ae1f05b202. Original implementation credit
and explanations are retained below. This IE-06 file retains only the active-injectivity and path-existence
argument; unrelated growth-bound lemmas and orthogonal corollaries are omitted.
-/
import NLA.IE06.Pivot
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The nonsingular-input path-existence obligation for IE-06.
The supported-vector injectivity proof is adapted from IE-04 at commit
286d8768fbd9a69264daa88e285680293db29837. No assertion is made that the padded
full intermediate matrix is nonsingular: only its active block is injective. -/

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal
namespace NLA.IE06

private theorem swap_active {n : ℕ} (k p i : Fin n) (hp : k ≤ p) (hi : k ≤ i) :
    k ≤ Equiv.swap k p i := by
  by_cases hik : i = k
  · subst i; simpa using hp
  · by_cases hip : i = p
    · subst i; simp
    · simpa [Equiv.swap_apply_of_ne_of_ne hik hip] using hi

/-- Kernel injectivity of the genuine active block, encoded without dependent matrices. -/
def ActiveInjective {n : ℕ} (S : Mat n) (k : ℕ) : Prop :=
  ∀ x : Fin n → ℝ, (∀ j, j.val < k → x j = 0) →
    (∀ i, k ≤ i.val → S.mulVec x i = 0) → x = 0

theorem activeInjective_initial_proved {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    ActiveInjective A 0 := by
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.mpr hA)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
  intro x _ hx
  apply hinj
  funext i
  simpa only [Matrix.mulVec_zero, Pi.zero_apply] using hx i (Nat.zero_le _)

theorem activeInjective_nonzero_column_proved {n : ℕ} (S : Mat n) (k : Fin n)
    (hS : ActiveInjective S k.val) : ∃ i, k ≤ i ∧ S i k ≠ 0 := by
  by_contra h
  have hz : ∀ i, k ≤ i → S i k = 0 := by
    intro i hi
    by_contra hne
    exact h ⟨i,hi,hne⟩
  have hsupp : ∀ j : Fin n, j.val < k.val → (Pi.single k (1:ℝ) : Fin n → ℝ) j = 0 := by
    intro j hj
    have hne : j ≠ k := by intro he; subst j; omega
    simp [hne]
  have he := hS (Pi.single k 1) hsupp (by
    intro i hi
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hz i hi)
  have hc := congrFun he k
  simp at hc

theorem activeInjective_rowSwap_proved {n : ℕ} (S : Mat n) (k p : Fin n)
    (hp : k ≤ p) (hS : ActiveInjective S k.val) : ActiveInjective (rowSwap S k p) k.val := by
  intro x hx hrows
  apply hS x hx
  intro i hi
  have hs := hrows (Equiv.swap k p i) (swap_active k p i hp hi)
  change S.mulVec x (Equiv.swap k p (Equiv.swap k p i)) = 0 at hs
  simpa using hs

theorem schurStep_mulVec_proved {n : ℕ} (S : Mat n) (k p i : Fin n)
    (x : Fin n → ℝ) (hx : ∀ j, j.val < k.val+1 → x j = 0) (hi : k < i) :
    (schurStep S k p).mulVec x i =
      (rowSwap S k p).mulVec x i -
        ((rowSwap S k p) i k / (rowSwap S k p) k k) * (rowSwap S k p).mulVec x k := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : k < j
  · simp only [schurStep, hi, hj, and_self, if_true]
    ring
  · have hz := hx j (by exact Nat.lt_succ_of_le (le_of_not_gt hj))
    simp [hz]

theorem activeInjective_schur_proved {n : ℕ} (S : Mat n) (k p : Fin n)
    (hp : k ≤ p) (hne : S p k ≠ 0) (hS : ActiveInjective S k.val) :
    ActiveInjective (schurStep S k p) (k.val+1) := by
  let B := rowSwap S k p
  have hB := activeInjective_rowSwap_proved S k p hp hS
  have hkk : B k k ≠ 0 := by simpa [B, rowSwap] using hne
  intro x hx hrows
  let c : ℝ := -(B.mulVec x k) / B k k
  let y : Fin n → ℝ := x + Pi.single k c
  have hysupp : ∀ j : Fin n, j.val < k.val → y j = 0 := by
    intro j hj
    have hne : j ≠ k := by intro he; subst j; omega
    simp [y, hne, hx j (by omega)]
  have hmul : ∀ i, B.mulVec y i = B.mulVec x i + B i k * c := by
    intro i
    simp [y, Matrix.mulVec_add, mul_comm]
  have hyrows : ∀ i, k.val ≤ i.val → B.mulVec y i = 0 := by
    intro i hi
    rw [hmul]
    by_cases hik : i = k
    · subst i
      dsimp [c]
      field_simp
      ring
    · have hki : k < i := by exact lt_of_le_of_ne hi (Ne.symm hik)
      have hz := hrows i (by exact hki)
      rw [schurStep_mulVec_proved S k p i x hx hki] at hz
      change B.mulVec x i - (B i k / B k k) * B.mulVec x k = 0 at hz
      calc
        B.mulVec x i + B i k * c = B.mulVec x i - (B i k / B k k) * B.mulVec x k := by dsimp [c]; ring
        _ = 0 := hz
  have hy := hB y hysupp hyrows
  funext j
  by_cases hj : j = k
  · subst j; exact hx k (Nat.lt_succ_self _)
  · have h := congrFun hy j
    simpa [y, Pi.single_apply, hj] using h

theorem firstTrajectory_activeInjective_proved {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (k : ℕ) (hk : k ≤ n) : ActiveInjective (firstTrajectory A k) k := by
  induction k with
  | zero => exact activeInjective_initial_proved A hA
  | succ k ih =>
    have hkn : k < n := by omega
    have hS := ih (Nat.le_of_lt hkn)
    have hp := firstPivotIndex_firstAvailable_proved (firstTrajectory A k) ⟨k,hkn⟩
      (activeInjective_nonzero_column_proved _ _ hS)
    simpa only [firstTrajectory, dif_pos hkn] using
      activeInjective_schur_proved (firstTrajectory A k) ⟨k,hkn⟩ _ hp.1.1 hp.1.2.1 hS

theorem firstPath_semantics_proved {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    FirstAvailablePath A (firstPath A) ∧
      (∀ k, trajectory A (firstPath A) k = firstTrajectory A k) ∧
      ∀ path, FirstAvailablePath A path → path = firstPath A := by
  refine ⟨?_, trajectory_firstPath_eq_proved A, firstPath_eq_of_firstAvailable_proved A⟩
  intro k
  have hp := firstPivotIndex_firstAvailable_proved (firstTrajectory A k.val) k
    (activeInjective_nonzero_column_proved _ _
      (firstTrajectory_activeInjective_proved A hA k.val (Nat.le_of_lt k.isLt)))
  simpa only [trajectory_firstPath_eq_proved, firstPath] using hp

/-- The canonical scan constructs an admissible path for every nonsingular
matrix, including the vacuous path in dimension zero. -/
theorem firstPath_admissible_proved {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    AdmissiblePath A (firstPath A) := by
  intro k
  exact ((firstPath_semantics_proved A hA).1 k).1

/-- Exact unconditional semantic obligation from the reviewed Challenge. -/
theorem admissiblePath_exists_proved {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    ∃ path : PivotPath n, AdmissiblePath A path :=
  ⟨firstPath A, firstPath_admissible_proved A hA⟩

#assert_trust kernel activeInjective_initial_proved
#print axioms activeInjective_initial_proved
#assert_trust kernel activeInjective_nonzero_column_proved
#print axioms activeInjective_nonzero_column_proved
#assert_trust kernel activeInjective_rowSwap_proved
#print axioms activeInjective_rowSwap_proved
#assert_trust kernel schurStep_mulVec_proved
#print axioms schurStep_mulVec_proved
#assert_trust kernel activeInjective_schur_proved
#print axioms activeInjective_schur_proved
#assert_trust kernel firstTrajectory_activeInjective_proved
#print axioms firstTrajectory_activeInjective_proved
#assert_trust kernel firstPath_semantics_proved
#print axioms firstPath_semantics_proved
#assert_trust kernel firstPath_admissible_proved
#print axioms firstPath_admissible_proved
#assert_trust kernel admissiblePath_exists_proved
#print axioms admissiblePath_exists_proved

end NLA.IE06
