/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
Complex adaptation of the repository IE-05 finite-maximum and active-block proofs.
-/
import NLA.IE14.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Finset.Max

noncomputable section
open scoped BigOperators NNReal
namespace NLA.IE14

/-- Kernel injectivity of the genuine active block, encoded without dependent matrices. -/
def ActiveInjective {n : ℕ} (S : Mat n) (k : ℕ) : Prop :=
  ∀ x : Fin n → ℂ, (∀ j, j.val < k → x j = 0) →
    (∀ i, k ≤ i.val → S.mulVec x i = 0) → x = 0

theorem activeInjective_initial {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    ActiveInjective A 0 := by
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.mpr hA)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
  intro x _ hx
  apply hinj
  funext i
  simpa only [Matrix.mulVec_zero, Pi.zero_apply] using hx i (Nat.zero_le _)

theorem activeInjective_nonzero_column {n : ℕ} (S : Mat n) (k : Fin n)
    (hS : ActiveInjective S k.val) : ∃ i, k ≤ i ∧ S i k ≠ 0 := by
  by_contra h
  have hz : ∀ i, k ≤ i → S i k = 0 := by
    intro i hi
    by_contra hne
    exact h ⟨i,hi,hne⟩
  have hsupp : ∀ j : Fin n, j.val < k.val → (Pi.single k (1:ℂ) : Fin n → ℂ) j = 0 := by
    intro j hj
    have hne : j ≠ k := by intro he; subst j; omega
    simp [hne]
  have he := hS (Pi.single k 1) hsupp (by
    intro i hi
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hz i hi)
  have hc := congrFun he k
  simp at hc

theorem activeInjective_rowSwap {n : ℕ} (S : Mat n) (k p : Fin n)
    (hp : k ≤ p) (hS : ActiveInjective S k.val) : ActiveInjective (rowSwap S k p) k.val := by
  intro x hx hrows
  apply hS x hx
  intro i hi
  have hs := hrows (Equiv.swap k p i) (swap_active k p i hp hi)
  change S.mulVec x (Equiv.swap k p (Equiv.swap k p i)) = 0 at hs
  simpa using hs

theorem schurStep_mulVec {n : ℕ} (S : Mat n) (k p i : Fin n)
    (x : Fin n → ℂ) (hx : ∀ j, j.val < k.val+1 → x j = 0) (hi : k < i) :
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

theorem activeInjective_schur {n : ℕ} (S : Mat n) (k p : Fin n)
    (hp : k ≤ p) (hne : S p k ≠ 0) (hS : ActiveInjective S k.val) :
    ActiveInjective (schurStep S k p) (k.val+1) := by
  let B := rowSwap S k p
  have hB := activeInjective_rowSwap S k p hp hS
  have hkk : B k k ≠ 0 := by simpa [B, rowSwap] using hne
  intro x hx hrows
  let c : ℂ := -(B.mulVec x k) / B k k
  let y : Fin n → ℂ := x + Pi.single k c
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
      rw [schurStep_mulVec S k p i x hx hki] at hz
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


/-- Select an actual maximal-modulus active entry; no deterministic tie restriction
is imposed on the public family of paths. -/
def maxPivot {n : ℕ} (S : Mat n) (k : Fin n) : Fin n :=
  Classical.choose (Finset.exists_max_image (Finset.univ.filter (k ≤ ·))
    (fun i => ‖S i k‖) ⟨k, by simp⟩)

theorem maxPivot_admissible {n : ℕ} (S : Mat n) (k : Fin n)
    (hS : ActiveInjective S k.val) : AdmissiblePivot S k (maxPivot S k) := by
  have hs := Classical.choose_spec (Finset.exists_max_image
    (Finset.univ.filter (k ≤ ·)) (fun i => ‖S i k‖) ⟨k, by simp⟩)
  change maxPivot S k ∈ Finset.univ.filter (k ≤ ·) ∧
    ∀ i ∈ Finset.univ.filter (k ≤ ·), ‖S i k‖ ≤ ‖S (maxPivot S k) k‖ at hs
  have hm : ∀ i, k ≤ i → ‖S i k‖ ≤ ‖S (maxPivot S k) k‖ := by
    intro i hi
    exact hs.2 i (by simp [hi])
  obtain ⟨i, hi, hne⟩ := activeInjective_nonzero_column S k hS
  refine ⟨by simpa using hs.1, ?_, hm⟩
  exact norm_pos_iff.mp (lt_of_lt_of_le (norm_pos_iff.mpr hne) (hm i hi))

def maxTrajectory {n : ℕ} (A : Mat n) : ℕ → Mat n
  | 0 => A
  | k+1 => if h : k<n then
      schurStep (maxTrajectory A k) ⟨k,h⟩ (maxPivot (maxTrajectory A k) ⟨k,h⟩)
    else 0

def maxPath {n : ℕ} (A : Mat n) : PivotPath n :=
  fun k => maxPivot (maxTrajectory A k.val) k

theorem trajectory_maxPath {n : ℕ} (A : Mat n) (k : ℕ) :
    trajectory A (maxPath A) k = maxTrajectory A k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [trajectory, maxTrajectory, maxPath, ih]

theorem maxTrajectory_activeInjective {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (k : ℕ) (hk : k ≤ n) : ActiveInjective (maxTrajectory A k) k := by
  induction k with
  | zero => exact activeInjective_initial A hA
  | succ k ih =>
    have hkn : k < n := by omega
    have hS := ih (by omega)
    have hp := maxPivot_admissible (maxTrajectory A k) ⟨k,hkn⟩ hS
    simpa only [maxTrajectory, dif_pos hkn] using
      activeInjective_schur (maxTrajectory A k) ⟨k,hkn⟩ _ hp.1 hp.2.1 hS

theorem admissible_path_exists_proved {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    ∃ path : PivotPath n, AdmissiblePath A path := by
  refine ⟨maxPath A, ?_⟩
  intro k
  rw [trajectory_maxPath]
  exact maxPivot_admissible _ k (maxTrajectory_activeInjective A hA k.val k.isLt.le)

end NLA.IE14
