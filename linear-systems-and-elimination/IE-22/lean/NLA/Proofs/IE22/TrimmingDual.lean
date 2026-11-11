import NLA.Proofs.IE22.EnergyBounds

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.IE22

/-- A minimum-energy finite row set is separated from its complement by a
nonnegative threshold. No sorting convention or real supremum is used. -/
theorem exists_trimming_cut {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    ∃ S : Finset ι, ∃ t : ℝ,
      S.card = k ∧ 0 ≤ t ∧
      (k : ℝ)*t - ∑ i, max (t-y i) 0 = ∑ i ∈ S, y i ∧
      ((Fintype.card ι-k+1 : ℕ) : ℝ)*t ≤ ∑ i, y i := by
  classical
  by_cases hk0 : k = 0
  · subst k
    refine ⟨∅, 0, by simp, le_rfl, ?_, ?_⟩
    · simp only [Nat.cast_zero, zero_mul, Finset.sum_empty, zero_sub, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro i _
      exact max_eq_right (by linarith [hy i])
    · simpa using Finset.sum_nonneg (fun i _ => hy i)
  let F : Finset (Finset ι) := Finset.univ.powersetCard k
  have hF : F.Nonempty := Finset.powersetCard_nonempty_of_le (by simpa using hk)
  obtain ⟨S, hSF, hmin⟩ := Finset.exists_min_image F (fun S => ∑ i ∈ S, y i) hF
  have hcard : S.card = k := (Finset.mem_powersetCard.mp hSF).2
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcross : ∀ i ∈ S, ∀ j, j ∉ S → y i ≤ y j := by
    intro i hi j hj
    have hje : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    have hT : insert j (S.erase i) ∈ F := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem hje, Finset.card_erase_of_mem hi, hcard]
      omega
    have h := hmin (insert j (S.erase i)) hT
    rw [Finset.sum_insert hje] at h
    have he := Finset.sum_erase_add S y hi
    linarith
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image S y hSne
  let t := y i
  have hselected : ∀ j ∈ S, y j ≤ t := hmax
  have houtside : ∀ j, j ∉ S → t ≤ y j := hcross i hi
  have hsum : ∑ j, max (t-y j) 0 = (k : ℝ)*t - ∑ j ∈ S, y j := by
    have hz : ∑ j ∈ S, max (t-y j) 0 = ∑ j, max (t-y j) 0 := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      exact max_eq_right (sub_nonpos.mpr (houtside j hj))
    rw [← hz]
    calc
      _ = ∑ j ∈ S, (t-y j) := Finset.sum_congr rfl (fun j hj =>
        max_eq_left (sub_nonneg.mpr (hselected j hj)))
      _ = _ := by rw [Finset.sum_sub_distrib]; simp [hcard]
  have hsumBound : ((Fintype.card ι-k+1 : ℕ) : ℝ)*t ≤ ∑ j, y j := by
    let U := insert i (Finset.univ \ S)
    have hiU : i ∉ (Finset.univ \ S : Finset ι) := by simp [hi]
    have hUcard : U.card = Fintype.card ι-k+1 := by
      dsimp [U]
      rw [Finset.card_insert_of_notMem hiU, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simp [hcard]
    have hlow : ∀ j ∈ U, t ≤ y j := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact le_rfl
      · exact houtside j (Finset.mem_sdiff.mp hj).2
    calc
      _ = ∑ j ∈ U, t := by simp [hUcard]
      _ ≤ ∑ j ∈ U, y j := Finset.sum_le_sum hlow
      _ ≤ ∑ j, y j := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ U) (fun j _ _ => hy j)
  refine ⟨S, t, hcard, hy i, ?_, hsumBound⟩
  rw [hsum]
  ring

/-- Under an average-energy bound, the exact finite trimming dual is
attained in the bounded interval used by the Gaussian argument. -/
theorem exists_bounded_trimming_cut {m : ℕ} (hm : 0 < m)
    {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (henergy : ∑ i, y i ≤ C*(m : ℝ)) :
    ∃ S : Finset (Fin m), ∃ t : ℝ,
      S.card = NLA.Statements.RowDeletion.RetainedCount θ m ∧
      0 ≤ t ∧ t ≤ C/(1-θ) ∧
      ((S.card : ℕ) : ℝ)*t - ∑ i, max (t-y i) 0 = ∑ i ∈ S, y i := by
  let k := NLA.Statements.RowDeletion.RetainedCount θ m
  have hk : k ≤ m := retainedCount_le hθ1.le m
  obtain ⟨S,t,hS,ht,hdual,hcount⟩ := exists_trimming_cut y hy k (by simpa using hk)
  have hfloor : (k : ℝ) ≤ θ*(m : ℝ) := by
    dsimp [k, NLA.Statements.RowDeletion.RetainedCount]
    exact Nat.floor_le (mul_nonneg hθ0 (Nat.cast_nonneg m))
  have hcount' : ((m : ℝ)-(k : ℝ)+1)*t ≤ C*(m : ℝ) := by
    have heq : ((Fintype.card (Fin m)-k+1 : ℕ) : ℝ) = (m : ℝ)-(k : ℝ)+1 := by
      simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk]
    rw [heq] at hcount
    exact hcount.trans henergy
  have hcoeff : (1-θ)*(m : ℝ) ≤ (m : ℝ)-(k : ℝ)+1 := by nlinarith
  have hprod := (mul_le_mul_of_nonneg_right hcoeff ht).trans hcount'
  have hfirst : (1-θ)*t ≤ C := by
    apply (mul_le_mul_iff_right₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mp
    nlinarith [hprod]
  refine ⟨S,t,hS,ht,(le_div_iff₀ (sub_pos.mpr hθ1)).2 ?_, ?_⟩
  · nlinarith [hfirst]
  · simpa only [hS] using hdual

#assert_trust kernel exists_bounded_trimming_cut
#assert_trust kernel exists_trimming_cut
#print axioms exists_trimming_cut
end NLA.Proofs.IE22
