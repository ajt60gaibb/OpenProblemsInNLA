import NLA.Proofs.TR04.SVDTieGate

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

theorem prefix_weights_eq_one {p r : ℕ} (hr : r ≤ p) (w : Fin p → ℝ)
    (hw : ∀ k, w k ≤ 1) (hsum : (∑ k, w k) = r)
    (hz : ∀ k, r ≤ k.val → w k = 0) : ∀ k, k.val < r → w k = 1 := by
  have hterm (k : Fin p) : (if k.val < r then 1 - w k else 0) =
      (if k.val < r then (1 : ℝ) else 0) - w k := by
    by_cases hk : k.val < r
    · simp [hk]
    · simp [hk, hz k (Nat.le_of_not_gt hk)]
  have htotal : (∑ k, if k.val < r then 1 - w k else 0) = 0 := by
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, prefix_count_of_le hr, hsum, sub_self]
  have hn (k : Fin p) : 0 ≤ (if k.val < r then 1 - w k else 0) := by
    split_ifs <;> linarith [hw k]
  intro k hk
  have hle := Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ k)
  rw [htotal, if_pos hk] at hle
  linarith [hw k]

theorem validSVD_equality_sum_projectionWeights {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) (a : Fin (min m l)) (ha : 0 < sigma a)
    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) :
    (∑ k : Fin (min m l), projectionWeight (columnSpace Y) U
      (Fin.castLE (Nat.min_le_left m l) k)) = a.val + 1 := by
  let S := columnSpace Y
  let w : Fin (min m l) → ℝ := fun k => projectionWeight S U
    (Fin.castLE (Nat.min_le_left m l) k)
  have hr : a.val + 1 ≤ min m l := by omega
  have hsum : ∑ k, w k ≤ a.val + 1 :=
    (sum_svd_projectionWeight_le S h.1).trans (by exact_mod_cast
      ((finrank_columnSpace Y).trans_le hY))
  have hab (k : Fin (min m l)) (hk : k.val < a.val + 1) : (sigma a)^2 ≤ (sigma k)^2 := by
    have hc := h.2.2.2.1 k a (Fin.le_iff_val_le_val.mpr (by omega))
    have := h.2.2.1 k
    nlinarith
  have hbe (k : Fin (min m l)) (hk : a.val + 1 ≤ k.val) : (sigma k)^2 ≤ (sigma a)^2 := by
    have hc := h.2.2.2.1 a k (Fin.le_iff_val_le_val.mpr (by omega))
    have := h.2.2.1 k
    nlinarith
  have hsum' : (∑ k, w k) ≤ ((a.val + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsum
  have hc := weighted_threshold_le (w := w) hr (sq_nonneg (sigma a)) hab hbe
    (fun k => projectionWeight_nonneg S U _) (fun k => projectionWeight_le_one S h.1 _) hsum'
  have hcap : matrixEnergy (projectMatrix S B) ≤
      prefixEnergy (fun k => (sigma k)^2) (a.val + 1) := by
    rw [validSVD_project_energy h]
    exact hc
  have hp := projectMatrix_energy_decomposition S B
  have he := projectMatrix_error_le S B Y (matrixColumn_mem_columnSpace Y)
  have ht := validSVD_energy h
  have htail := prefix_add_tail sigma (a.val + 1)
  have hceq : (∑ k, (sigma k)^2 * w k) = prefixEnergy (fun k => (sigma k)^2) (a.val + 1) := by
    rw [← validSVD_project_energy h S]
    linarith
  simpa only [Nat.cast_add, Nat.cast_one] using (weighted_threshold_eq_support (w := w) hr (sq_pos_of_pos ha) hab hbe
    (fun k => projectionWeight_nonneg S U _) (fun k => projectionWeight_le_one S h.1 _)
    hsum' hceq).1

/-- If the full threshold block is retained, every tested projector annihilates
the equality comparator residual. This covers the no-crossing-tie case. -/
theorem TieStructure.full_equality_residual_zero {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) {a : Fin (min m l)} (T : TieStructure sigma a)
    (ha : 0 < sigma a) (hfull : T.take = T.tied)
    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) (j : Fin T.tied) :
    projectMatrix (directionSubspace U (tieSelection T.above T.tied T.fits T.take j))
      (B - Y) = 0 := by
  have hs := validSVD_eckartYoung_eq_last_retained h a ha Y hY heq
  let w : Fin (min m l) → ℝ := fun k => projectionWeight (columnSpace Y) U
    (Fin.castLE (Nat.min_le_left m l) k)
  have hrt : T.above + T.tied = a.val + 1 := by rw [← hfull, T.rank_eq]
  have hz (k : Fin (min m l)) (hk : a.val + 1 ≤ k.val) : w k = 0 := by
    have hlt : sigma k < sigma a := by
      have hle : sigma k ≤ sigma a := by
        by_contra hn
        have hh := (T.above_iff k).mp (lt_of_not_ge hn)
        omega
      have hne : sigma k ≠ sigma a := by
        intro he
        have hh := (T.equal_iff k).mp he
        omega
      exact lt_of_le_of_ne hle hne
    exact (projectionWeight_eq_zero_iff _ U _).mpr (hs.2.2.2 k hlt)
  have hsum' : (∑ k, w k) = ((a.val + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using validSVD_equality_sum_projectionWeights h a ha Y hY heq
  have hone := prefix_weights_eq_one (by omega : a.val + 1 ≤ min m l) w
    (fun k => projectionWeight_le_one _ h.1 _) hsum' hz
  have hsub : directionSubspace U (tieSelection T.above T.tied T.fits T.take j) ≤ columnSpace Y := by
    apply singularSubspace_le
    intro k hk
    have hv := tieSelection_val_lt T.fits T.take j k hk
    have hw1 := hone k (by omega)
    exact (columnSpace Y).starProjection_eq_self_iff.mp
      ((projectionWeight_eq_one_iff _ h.1 _).mp hw1)
  rw [hs.1]
  exact projectMatrix_residual_eq_zero_of_le _ _ hsub B

theorem TieStructure.equality_exists_strict_residual {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) {a : Fin (min m l)} (T : TieStructure sigma a)
    (ha : 0 < sigma a) (Y : Matrix (Fin m) (Fin l) ℝ)
    (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1))
    (hpos : 0 < matrixEnergy (B - Y)) :
    ∃ j : Fin T.tied, matrixEnergy (projectMatrix
      (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) (B - Y)) <
        matrixEnergy (B - Y) := by
  by_cases hfull : T.take = T.tied
  · let j : Fin T.tied := ⟨0, T.tied_pos⟩
    refine ⟨j, ?_⟩
    rw [T.full_equality_residual_zero h ha hfull Y hY heq j]
    simpa only [matrixEnergy, Matrix.zero_apply, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero] using hpos
  · obtain ⟨j, hj⟩ := T.equality_exists_small_residual h ha Y hY heq
    refine ⟨j, hj.trans_lt ?_⟩
    have ht : 0 < (T.tied : ℝ) := by exact_mod_cast T.tied_pos
    have hs : (T.take : ℝ) < T.tied := by exact_mod_cast (lt_of_le_of_ne T.take_le hfull)
    have hf : (T.take : ℝ) / T.tied < 1 := (div_lt_one ht).mpr hs
    nlinarith

#assert_trust kernel TieStructure.full_equality_residual_zero
#assert_trust kernel TieStructure.equality_exists_strict_residual
#print axioms TieStructure.equality_exists_strict_residual
end NLA.Proofs.TR04.SVD
