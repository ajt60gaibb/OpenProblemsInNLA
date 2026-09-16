/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The generic GEPP implementation below is adapted from IE-05 at upstream
8f04b905eb2e0827b6b84f37d9d080ae1f05b202. Original implementation credit
and explanations are retained below. Only namespace/imports change; the
IE-05-specific orthogonal growth-set corollary is omitted from GEPP.lean.
-/
import NLA.IE04.Pivot
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Finset.Max

/-!
# Genuine GEPP semantics and the all-path growth bound

Finite entry maxima are proved directly from the frozen NNReal supremum.
Nonsingularity is maintained as injectivity on vectors supported in the active
block, never as a determinant assertion about the zero-padded full matrix.
Implementation: formal_review_standards AI agent for George Stepaniants;
the coordinator suggested the supported-vector injectivity route.
-/

noncomputable section
open scoped BigOperators NNReal
namespace NLA.IE04

theorem entryMax_nonneg_proved {n : ℕ} (A : Mat n) : 0 ≤ entryMax A :=
  (entryMaxNN A).coe_nonneg

theorem activeMax_nonneg_proved {n : ℕ} (S : Mat n) (k : ℕ) : 0 ≤ activeMax S k :=
  (activeMaxNN S k).coe_nonneg

theorem abs_le_entryMax_proved {n : ℕ} (A : Mat n) (i j : Fin n) :
    |A i j| ≤ entryMax A := by
  have h : ‖A i j‖₊ ≤ entryMaxNN A :=
    Finset.le_sup (f := fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) (Finset.mem_univ (i, j))
  have hc := NNReal.coe_le_coe.mpr h
  simpa only [coe_nnnorm, Real.norm_eq_abs, entryMax] using hc

theorem abs_le_activeMax_proved {n : ℕ} (S : Mat n) (k : ℕ) (i j : Fin n)
    (hi : k ≤ i.val) (hj : k ≤ j.val) : |S i j| ≤ activeMax S k := by
  have h : ‖S i j‖₊ ≤ activeMaxNN S k := by
    simpa only [activeMaxNN, hi, hj, and_self, if_true] using
      (Finset.le_sup (s := Finset.univ)
        (f := fun ij : Fin n × Fin n =>
          if k ≤ ij.1.val ∧ k ≤ ij.2.val then ‖S ij.1 ij.2‖₊ else 0)
        (Finset.mem_univ (i, j)))
  have hc := NNReal.coe_le_coe.mpr h
  simpa only [coe_nnnorm, Real.norm_eq_abs, activeMax] using hc

theorem activeMax_le_proved {n : ℕ} (S : Mat n) (k : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ i j, k ≤ i.val → k ≤ j.val → |S i j| ≤ C) :
    activeMax S k ≤ C := by
  have hnn : activeMaxNN S k ≤ ⟨C, hC⟩ := by
    apply Finset.sup_le
    intro ij _
    by_cases hij : k ≤ ij.1.val ∧ k ≤ ij.2.val
    · simp only [if_pos hij]
      apply NNReal.coe_le_coe.mp
      change ‖S ij.1 ij.2‖ ≤ C
      simpa only [Real.norm_eq_abs] using h ij.1 ij.2 hij.1 hij.2
    · simp only [if_neg hij]
      exact bot_le
  exact NNReal.coe_le_coe.mpr hnn

theorem entryMax_semantics_proved {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    0 ≤ entryMax A ∧ (∀ i j, |A i j| ≤ entryMax A) ∧
      ∃ i j, entryMax A = |A i j| := by
  refine ⟨entryMax_nonneg_proved A, abs_le_entryMax_proved A, ?_⟩
  let z : Fin n := ⟨0, by omega⟩
  obtain ⟨ij, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun ij => ‖A ij.1 ij.2‖₊) ⟨(z, z), Finset.mem_univ _⟩
  have he : entryMaxNN A = ‖A ij.1 ij.2‖₊ :=
    le_antisymm (Finset.sup_le hmax)
      (Finset.le_sup (f := fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) (Finset.mem_univ ij))
  refine ⟨ij.1, ij.2, ?_⟩
  simpa only [entryMax, coe_nnnorm, Real.norm_eq_abs] using congrArg NNReal.toReal he

theorem activeMax_zero_proved {n : ℕ} (S : Mat n) : activeMax S 0 = entryMax S := by
  simp [activeMax, activeMaxNN, entryMax, entryMaxNN]

private theorem swap_active {n : ℕ} (k p i : Fin n) (hp : k ≤ p) (hi : k ≤ i) :
    k ≤ Equiv.swap k p i := by
  by_cases hik : i = k
  · subst i; simpa using hp
  · by_cases hip : i = p
    · subst i; simp
    · simpa [Equiv.swap_apply_of_ne_of_ne hik hip] using hi

theorem schurStep_bound_proved {n : ℕ} (S : Mat n) (k p : Fin n)
    (hp : AdmissiblePivot S k p) :
    activeMax (schurStep S k p) (k.val + 1) ≤ 2 * activeMax S k.val := by
  let B := rowSwap S k p
  let M := activeMax S k.val
  have hM : 0 ≤ M := activeMax_nonneg_proved S k.val
  have hb : ∀ i j, k ≤ i → k ≤ j → |B i j| ≤ M := by
    intro i j hi hj
    exact abs_le_activeMax_proved S k.val (Equiv.swap k p i) j (swap_active k p i hp.1 hi) hj
  have hkk : B k k = S p k := by simp [B, rowSwap]
  have hpos : 0 < |B k k| := abs_pos.mpr (hkk ▸ hp.2.1)
  apply activeMax_le_proved _ _ _ (mul_nonneg (by norm_num) hM)
  intro i j hi hj
  have hki : k < i := by exact hi
  have hkj : k < j := by exact hj
  have hmult : |B i k / B k k| ≤ 1 := by
    rw [abs_div, div_le_one hpos]
    rw [hkk]
    exact hp.2.2 _ (swap_active k p i hp.1 hki.le)
  change |(if k < i ∧ k < j then B i j - (B i k / B k k) * B k j else 0)| ≤ 2 * M
  rw [if_pos ⟨hki, hkj⟩]
  calc
    |B i j - (B i k / B k k) * B k j| ≤ |B i j| + |(B i k / B k k) * B k j| := by
      simpa using abs_sub_le (B i j) 0 ((B i k / B k k) * B k j)
    _ = |B i j| + |B i k / B k k| * |B k j| := by rw [abs_mul]
    _ ≤ M + 1 * M := add_le_add (hb i j hki.le hkj.le)
      (mul_le_mul hmult (hb k j le_rfl hkj.le) (abs_nonneg _) (by norm_num))
    _ = 2 * M := by ring

/-- The actual finite numerator in the frozen definition of `growth`. -/
def peakMax {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ)

theorem activeMax_le_peakMax_proved {n : ℕ} (A : Mat n) (path : PivotPath n) (k : Fin n) :
    activeMax (trajectory A path k.val) k.val ≤ peakMax A path :=
  NNReal.coe_le_coe.mpr
    (Finset.le_sup (f := fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val) (Finset.mem_univ k))

theorem peakMax_le_proved {n : ℕ} (A : Mat n) (path : PivotPath n) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ k : Fin n, activeMax (trajectory A path k.val) k.val ≤ C) :
    peakMax A path ≤ C := by
  have hnn : (Finset.univ.sup (fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) ≤ ⟨C,hC⟩ := by
    apply Finset.sup_le
    intro k _
    exact NNReal.coe_le_coe.mp (h k)
  exact NNReal.coe_le_coe.mpr hnn

theorem entryMax_le_peakMax_proved {n : ℕ} (hn : 1 ≤ n) (A : Mat n) (path : PivotPath n) :
    entryMax A ≤ peakMax A path := by
  have h := activeMax_le_peakMax_proved A path (⟨0, by omega⟩ : Fin n)
  simpa only [trajectory, activeMax_zero_proved] using h

theorem gepp_stage_bound_proved {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hp : AdmissiblePath A path) (k : ℕ) (hk : k < n) :
    activeMax (trajectory A path k) k ≤ (2 : ℝ)^k * entryMax A := by
  induction k with
  | zero => simp [trajectory, activeMax_zero_proved]
  | succ k ih =>
    have hkn : k < n := by omega
    have hs := schurStep_bound_proved (trajectory A path k) ⟨k,hkn⟩ (path ⟨k,hkn⟩) (hp ⟨k,hkn⟩)
    calc
      activeMax (trajectory A path (k+1)) (k+1) ≤ 2 * activeMax (trajectory A path k) k := by
        simpa only [trajectory, dif_pos hkn] using hs
      _ ≤ 2 * ((2:ℝ)^k * entryMax A) := mul_le_mul_of_nonneg_left (ih hkn) (by norm_num)
      _ = (2:ℝ)^(k+1) * entryMax A := by ring

theorem gepp_growth_bound_proved {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (path : PivotPath n) (hp : AdmissiblePath A path) :
    0 < entryMax A ∧ 1 ≤ growth A path ∧ growth A path ≤ (2 : ℝ) ^ (n - 1) := by
  let z : Fin n := ⟨0, by omega⟩
  have hz : A (path z) z ≠ 0 := by simpa [z, trajectory] using (hp z).2.1
  have hE : 0 < entryMax A := lt_of_lt_of_le (abs_pos.mpr hz) (abs_le_entryMax_proved A (path z) z)
  have hpeak : peakMax A path ≤ (2:ℝ)^(n-1) * entryMax A := by
    apply peakMax_le_proved _ _ _ (mul_nonneg (by positivity) hE.le)
    intro k
    exact (gepp_stage_bound_proved A path hp k.val k.isLt).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)) hE.le)
  refine ⟨hE, ?_, ?_⟩
  · change 1 ≤ peakMax A path / entryMax A
    exact (le_div_iff₀ hE).2 (by simpa using entryMax_le_peakMax_proved hn A path)
  · change peakMax A path / entryMax A ≤ (2:ℝ)^(n-1)
    exact (div_le_iff₀ hE).2 hpeak

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

#assert_trust kernel entryMax_semantics_proved
#print axioms entryMax_semantics_proved
#assert_trust kernel schurStep_bound_proved
#print axioms schurStep_bound_proved
#assert_trust kernel gepp_growth_bound_proved
#print axioms gepp_growth_bound_proved
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

end NLA.IE04
