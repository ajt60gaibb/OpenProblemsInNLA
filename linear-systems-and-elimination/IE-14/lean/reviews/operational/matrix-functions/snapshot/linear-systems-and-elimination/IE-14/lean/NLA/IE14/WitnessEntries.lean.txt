/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE14.Tail

noncomputable section
open scoped BigOperators
namespace NLA.IE14

theorem lower_delta (n : ℕ) (i a : Fin n) :
    witnessLower n i a = (if a=i then 1 else 0) -
      (if a.val+1=i.val then 1 else 0) - (if a.val+2=i.val then 1 else 0) := by
  unfold witnessLower
  by_cases h : a=i
  · subst a
    simp
  · have h' : i ≠ a := Ne.symm h
    simp only [h,h',↓reduceIte]
    split_ifs <;> first | omega | ring

theorem sum_predecessor {n : ℕ} (d : ℕ) (i : Fin n) (f : Fin n → ℂ) :
    (∑ a : Fin n, if a.val+d=i.val then f a else 0) =
      if _h : d ≤ i.val then f ⟨i.val-d, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ else 0 := by
  by_cases hi : d ≤ i.val
  · rw [dif_pos hi, Finset.sum_eq_single ⟨i.val-d,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩]
    · simp [Nat.sub_add_cancel hi]
    · intro a _ ha
      have hne : a.val+d ≠ i.val := by
        intro he
        apply ha
        apply Fin.ext
        change a.val = i.val-d
        omega
      simp [hne]
    · simp
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro a _
    simp [show a.val+d ≠ i.val by omega]

theorem lower_mul (n : ℕ) (U : Mat n) (i j : Fin n) :
    (witnessLower n * U) i j = U i j -
      (if _h : 1 ≤ i.val then U ⟨i.val-1,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ j else 0) -
      (if _h : 2 ≤ i.val then U ⟨i.val-2,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ j else 0) := by
  simp only [Matrix.mul_apply, lower_delta, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [sum_predecessor 1, sum_predecessor 2]

theorem upper_nonfinal_column (n : ℕ) (a j : Fin n)
    (hj : j.val+1 ≠ n) (hj1 : j.val ≠ 1) :
    witnessUpper n a j = if a=j then 1 else 0 := by
  by_cases ha : a=j
  · subst a
    simp [witnessUpper,hj,hj1]
  · simp [witnessUpper,hj,ha,hj1]

theorem product_nonfinal_column (n : ℕ) (i j : Fin n)
    (hj : j.val+1 ≠ n) (hj1 : j.val ≠ 1) :
    (witnessLower n * witnessUpper n) i j = witnessLower n i j := by
  simp only [Matrix.mul_apply, upper_nonfinal_column n _ j hj hj1, mul_ite, mul_one, mul_zero]
  simp

theorem product_second_column (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) (hj : j.val=1) :
    (witnessLower n * witnessUpper n) i j =
      witnessLower n i ⟨0,by omega⟩ / 2 + witnessLower n i j / 2 := by
  let z : Fin n := ⟨0,by omega⟩
  have hn2 : (2 : ℕ) ≠ n := by omega
  have hcol : ∀ a : Fin n, witnessUpper n a j =
      (if a=z then (1/2:ℂ) else 0) + (if a=j then (1/2:ℂ) else 0) := by
    intro a
    have haz : a=z ↔ a.val=0 := by simp [z,Fin.ext_iff]
    by_cases haj : a=j
    · subst a
      simp [witnessUpper,hn2,hj,haz]
    · simp [witnessUpper,hn2,haj,hj,haz]
  simp only [Matrix.mul_apply,hcol,mul_add,Finset.sum_add_distrib,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  change witnessLower n i z * (1/2) + witnessLower n i j * (1/2) = _
  ring

theorem product_last_column (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) (hj : j.val+1=n) :
    (witnessLower n * witnessUpper n) i j =
      if i.val=0 ∨ i.val=1 ∨ i=j then 1 else 0 := by
  rw [lower_mul]
  by_cases hi0 : i.val=0
  · have hij : i ≠ j := by intro h; subst i; omega
    simp [witnessUpper,hj,hi0,hij,Nat.fib_add_two]
  · by_cases hi1 : i.val=1
    · have hij : i ≠ j := by intro h; subst i; omega
      have hzj : (⟨0,by omega⟩ : Fin n) ≠ j := by
        intro h
        have he : 0 = j.val := congrArg Fin.val h
        omega
      norm_num [witnessUpper,hj,hi1,hij,hzj,Nat.fib_add_two]
    · have hi2 : 2 ≤ i.val := by omega
      have hi' : 1 ≤ i.val := by omega
      have hsub1 : i.val-1+2=i.val+1 := by omega
      have hsub2 : i.val-2+2=i.val := by omega
      have hpj (d : ℕ) (hd : 0 < d) (hdi : d ≤ i.val) :
          (⟨i.val-d,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin n) ≠ j := by
        intro h
        have he : i.val-d = j.val := congrArg Fin.val h
        have := i.isLt
        omega
      simp only [dif_pos hi',dif_pos hi2,witnessUpper,hj,↓reduceIte,
        hpj 1 (by omega) hi',hpj 2 (by omega) hi2,hsub1,hsub2,
        hi0,hi1,false_or]
      have hf : (Nat.fib (i.val+2) : ℂ) = (Nat.fib i.val : ℂ) + (Nat.fib (i.val+1) : ℂ) := by
        exact_mod_cast (Nat.fib_add_two (n := i.val))
      by_cases hij : i=j
      · have hn' : n+1=i.val+2 := by subst i; omega
        simp only [if_pos hij,hn']
        rw [hf]
        ring
      · simp only [hij,↓reduceIte]
        rw [hf]
        ring

theorem product_second_values (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) (hj : j.val=1) :
    (witnessLower n * witnessUpper n) i j =
      if i.val=0 then 1/2 else if i.val=2 then -1 else if i.val=3 then -1/2 else 0 := by
  rw [product_second_column n hn i j hj]
  by_cases h0 : i.val=0
  · simp [witnessLower,Fin.ext_iff,hj,h0]
  · by_cases h1 : i.val=1
    · norm_num [witnessLower,Fin.ext_iff,hj,h1]
    · by_cases h2 : i.val=2
      · norm_num [witnessLower,Fin.ext_iff,hj,h2]
      · by_cases h3 : i.val=3
        · norm_num [witnessLower,Fin.ext_iff,hj,h3]
        · simp [witnessLower,Fin.ext_iff,hj,h0,h1,h2,h3,eq_comm]

theorem product_norm_le_one (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) :
    ‖(witnessLower n * witnessUpper n) i j‖ ≤ 1 := by
  by_cases hj : j.val+1=n
  · rw [product_last_column n hn i j hj]
    split_ifs <;> norm_num
  · by_cases hj1 : j.val=1
    · rw [product_second_values n hn i j hj1]
      split_ifs
      · exact norm_half_complex_le_one
      · norm_num
      · simpa only [neg_div,norm_neg] using norm_half_complex_le_one
      · norm_num
    · rw [product_nonfinal_column n i j hj hj1]
      exact lower_norm n i j

theorem lower_support (n : ℕ) (i j : Fin n) (h : witnessLower n i j ≠ 0) :
    j.val ≤ i.val ∧ i.val ≤ j.val+2 := by
  unfold witnessLower at h
  split_ifs at h with he hsub
  · subst i; omega
  · rcases hsub with hsub | hsub <;> omega
  · exact False.elim (h rfl)

theorem witness_forbidden_zero (n : ℕ) (hn : 4 ≤ n) (i j : Fin n)
    (hij : ¬CyclicPosition i j) : witnessMatrix n hn i j=0 := by
  unfold witnessMatrix
  by_cases hj : j.val+1=n
  · rw [product_last_column n hn _ j hj]
    split_ifs with h
    · exfalso
      unfold CyclicPosition at hij
      simp only [Fin.ext_iff] at h
      dsimp only [factorIndex] at h
      split_ifs at h <;> simp only [false_or] at h <;> omega
    · rfl
  · by_cases hj1 : j.val=1
    · rw [product_second_values n hn _ j hj1]
      split_ifs with h0 h2 h3
      all_goals try rfl
      all_goals
        exfalso
        unfold CyclicPosition at hij
        dsimp only [factorIndex] at *
        split_ifs at * <;> simp only at * <;> omega
    · rw [product_nonfinal_column n _ j hj hj1]
      by_contra h
      have hs := lower_support n (factorIndex n hn i) j h
      unfold CyclicPosition at hij
      dsimp only [factorIndex] at hs
      split_ifs at hs <;> simp only at hs <;> omega

theorem witness_corners (n : ℕ) (hn : 4 ≤ n) (i j : Fin n)
    (hi : i.val=0) (hj : j.val+1=n) :
    witnessMatrix n hn i j=1 ∧ witnessMatrix n hn j i = -1 := by
  constructor
  · unfold witnessMatrix
    rw [product_last_column n hn _ j hj]
    simp [factorIndex,hi]
  · unfold witnessMatrix
    rw [product_nonfinal_column n _ i (by omega) (by omega)]
    have hj0 : j.val ≠ 0 := by omega
    simp [factorIndex,hj,hj0,witnessLower,Fin.ext_iff,hi]

theorem witness_data_proved (n : ℕ) (hn : 4 ≤ n) :
    CyclicInput (witnessMatrix n hn) ∧ entryMax (witnessMatrix n hn)=1 := by
  have hc := witness_corners n hn
  have hbound : ∀ i j, ‖witnessMatrix n hn i j‖ ≤ 1 :=
    fun i j => product_norm_le_one n hn _ j
  refine ⟨⟨witness_det_ne_zero n hn, witness_forbidden_zero n hn, ?_⟩, ?_⟩
  · intro i j hi hj
    rw [(hc i j hi hj).1,(hc i j hi hj).2]
    norm_num
  · obtain ⟨_,_,i,j,he⟩ := entryMax_semantics (by omega : 1 ≤ n) (witnessMatrix n hn)
    apply le_antisymm
    · rw [he]
      exact hbound i j
    · have h := norm_le_entryMax (witnessMatrix n hn) ⟨0,by omega⟩ ⟨n-1,by omega⟩
      rw [(hc ⟨0,by omega⟩ ⟨n-1,by omega⟩ rfl (by simp;omega)).1] at h
      simpa only [norm_one] using h

end NLA.IE14
