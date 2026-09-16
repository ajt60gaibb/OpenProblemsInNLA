/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
Trailing-sum algebra adapts the existing IE-05 LU proof to complex scalars.
-/
import NLA.IE14.Factors

noncomputable section
open scoped BigOperators
namespace NLA.IE14

def tailEntry {n : ℕ} (L U : Mat n) (k : ℕ) (i j : Fin n) : ℂ :=
  ∑ a : Fin n, if k ≤ a.val then L i a * U a j else 0

theorem tail_zero {n : ℕ} (L U : Mat n) (i j : Fin n) :
    tailEntry L U 0 i j = (L*U) i j := by
  simp [tailEntry, Matrix.mul_apply]

theorem tail_pivot_row {n : ℕ} (L U : Mat n) (hL : L.IsLowerTriangular)
    (hd : ∀ i, L i i=1) (k j : Fin n) : tailEntry L U k.val k j = U k j := by
  unfold tailEntry
  rw [Finset.sum_eq_single k]
  · simp [hd]
  · intro a _ ha
    by_cases hka : k ≤ a
    · have hlt : k < a := lt_of_le_of_ne hka (Ne.symm ha)
      have hz : L k a=0 := hL hlt
      simp [hka, hz]
    · simp [hka]
  · simp

theorem tail_pivot_column {n : ℕ} (L U : Mat n) (hU : U.IsUpperTriangular)
    (k i : Fin n) : tailEntry L U k.val i k = L i k * U k k := by
  unfold tailEntry
  rw [Finset.sum_eq_single k]
  · simp
  · intro a _ ha
    by_cases hka : k ≤ a
    · have hlt : k < a := lt_of_le_of_ne hka (Ne.symm ha)
      have hz : U a k=0 := hU hlt
      simp [hka, hz]
    · simp [hka]
  · simp

theorem tail_split {n : ℕ} (L U : Mat n) (k i j : Fin n) :
    tailEntry L U k.val i j = L i k * U k j + tailEntry L U (k.val+1) i j := by
  unfold tailEntry
  calc
    (∑ a : Fin n, if k.val ≤ a.val then L i a * U a j else 0) =
        ∑ a : Fin n, ((if a=k then L i k * U k j else 0) +
          (if k.val+1 ≤ a.val then L i a * U a j else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a=k
      · subst a; simp
      · have hne : a.val ≠ k.val := fun h => ha (Fin.ext h)
        by_cases hka : k.val ≤ a.val
        · simp [ha,hka,show k.val+1 ≤ a.val by omega]
        · simp [ha,hka,show ¬k.val+1 ≤ a.val by omega]
    _ = L i k * U k j + ∑ a : Fin n,
        if k.val+1 ≤ a.val then L i a * U a j else 0 := by
      rw [Finset.sum_add_distrib]
      simp

/-- Factor-row labels at actual physical positions after the prescribed swaps. -/
def stageFactor (n : ℕ) (hn : 4 ≤ n) (k i : Fin n) : Fin n :=
  if k.val=0 then factorIndex n hn i
  else if hi : i.val+1=n then k else ⟨i.val+1, by omega⟩

theorem witnessPath_active (n : ℕ) (hn : 4 ≤ n) (k : Fin n) :
    k ≤ witnessPath n hn k := by
  unfold witnessPath
  split_ifs <;> simp only [Fin.le_def] <;> omega

theorem stageFactor_pivot (n : ℕ) (hn : 4 ≤ n) (k : Fin n) :
    stageFactor n hn k (witnessPath n hn k) = k := by
  by_cases hk : k.val=0
  · apply Fin.ext
    simp [witnessPath, stageFactor, factorIndex, hk]
  · have hl : n-1+1=n := by omega
    simp [witnessPath, stageFactor, hk, hl]

theorem stageFactor_swap_succ (n : ℕ) (hn : 4 ≤ n) (k i : Fin n)
    (hk : k.val + 1 < n) (hi : k < i) :
    stageFactor n hn k (Equiv.swap k (witnessPath n hn k) i) =
      stageFactor n hn ⟨k.val+1,hk⟩ i := by
  have hik : i ≠ k := ne_of_gt hi
  by_cases hz : k.val=0
  · simp only [witnessPath, hz, ↓reduceIte, Equiv.swap_self, Equiv.refl_apply]
    apply Fin.ext
    dsimp [stageFactor, factorIndex]
    split_ifs <;> omega
  · have hlast : n-1+1=n := by omega
    simp only [witnessPath, hz, ↓reduceIte]
    by_cases hilast : i = (⟨n-1,by omega⟩ : Fin n)
    · rw [hilast]
      rw [Equiv.swap_apply_right]
      apply Fin.ext
      simp [stageFactor, hz, hlast, show k.val+1 ≠ n by omega]
    · rw [Equiv.swap_apply_of_ne_of_ne hik hilast]
      have hi' : i.val+1 ≠ n := by
        intro h
        apply hilast
        apply Fin.ext
        change i.val = n-1
        omega
      simp [stageFactor, hz, hi']

/-- Full active-entry identity in the literal physical row order, not an assumed LU order. -/
theorem witness_trajectory (n : ℕ) (hn : 4 ≤ n) (k : ℕ) (hk : k < n)
    (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    trajectory (witnessMatrix n hn) (witnessPath n hn) k i j =
      tailEntry (witnessLower n) (witnessUpper n) k
        (stageFactor n hn ⟨k,hk⟩ i) j := by
  induction k generalizing i j with
  | zero => simp [trajectory, witnessMatrix, stageFactor, tail_zero]
  | succ k ih =>
    have hkn : k < n := by omega
    let q : Fin n := ⟨k,hkn⟩
    let p : Fin n := witnessPath n hn q
    let r : Fin n := Equiv.swap q p i
    have hq : q ≤ p := witnessPath_active n hn q
    have hir : k ≤ r.val := swap_active q p i hq (by exact Nat.le_of_succ_le hi)
    have hki : q < i := by exact hi
    have hkj : q < j := by exact hj
    have hpj := ih hkn p j hq (by omega)
    have hpk := ih hkn p q hq le_rfl
    have hrj := ih hkn r j hir (by omega)
    have hrk := ih hkn r q hir le_rfl
    have hlabel : stageFactor n hn q p=q := stageFactor_pivot n hn q
    rw [hlabel, tail_pivot_row _ _ (lower_triangular n) (lower_diag n) q j] at hpj
    rw [hlabel, tail_pivot_row _ _ (lower_triangular n) (lower_diag n) q q] at hpk
    rw [tail_pivot_column _ _ (upper_triangular n) q] at hrk
    rw [trajectory, dif_pos hkn]
    simp only [schurStep, rowSwap, Equiv.swap_apply_left]
    change (if q < i ∧ q < j then
      trajectory (witnessMatrix n hn) (witnessPath n hn) k r j -
        (trajectory (witnessMatrix n hn) (witnessPath n hn) k r q /
          trajectory (witnessMatrix n hn) (witnessPath n hn) k p q) *
            trajectory (witnessMatrix n hn) (witnessPath n hn) k p j else 0) = _
    rw [if_pos ⟨hki,hkj⟩, hrj, hrk, hpk, hpj]
    have hu := upper_diag_ne_zero n q
    rw [mul_div_cancel_right₀ _ hu]
    rw [tail_split _ _ q]
    have hl := stageFactor_swap_succ n hn q i hk hki
    change stageFactor n hn q r = stageFactor n hn ⟨k+1,hk⟩ i at hl
    rw [hl]
    ring

theorem witness_path_admissible (n : ℕ) (hn : 4 ≤ n) :
    AdmissiblePath (witnessMatrix n hn) (witnessPath n hn) := by
  intro k
  have hp := witnessPath_active n hn k
  have hcol : ∀ i, k ≤ i →
      trajectory (witnessMatrix n hn) (witnessPath n hn) k.val i k =
        witnessLower n (stageFactor n hn k i) k * witnessUpper n k k := by
    intro i hi
    rw [witness_trajectory n hn k.val k.isLt i k hi le_rfl,
      tail_pivot_column _ _ (upper_triangular n)]
  have hpiv : trajectory (witnessMatrix n hn) (witnessPath n hn) k.val
      (witnessPath n hn k) k = witnessUpper n k k := by
    rw [hcol _ hp, stageFactor_pivot, lower_diag, one_mul]
  refine ⟨hp, ?_, ?_⟩
  · rw [hpiv]
    exact upper_diag_ne_zero n k
  · intro i hi
    rw [hcol i hi, hpiv, norm_mul]
    exact (mul_le_mul_of_nonneg_right (lower_norm n _ _) (norm_nonneg _)).trans_eq (one_mul _)

theorem witness_final_scalar (n : ℕ) (hn : 4 ≤ n) :
    trajectory (witnessMatrix n hn) (witnessPath n hn) (n-1)
      ⟨n-1,by omega⟩ ⟨n-1,by omega⟩ = (Nat.fib (n+1) : ℂ)+1 := by
  let k : Fin n := ⟨n-1,by omega⟩
  have hk : n-1+1=n := by omega
  have hk0 : n-1 ≠ 0 := by omega
  rw [witness_trajectory n hn (n-1) k.isLt k k le_rfl le_rfl]
  have hf : stageFactor n hn k k=k := by simp [stageFactor,k,hk,hk0]
  rw [hf]
  change tailEntry (witnessLower n) (witnessUpper n) k.val k k = _
  rw [tail_pivot_row _ _ (lower_triangular n) (lower_diag n)]
  simp [witnessUpper,k,hk]

end NLA.IE14
