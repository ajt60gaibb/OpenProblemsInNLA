import ProofProject.BasisEnergy

/-! Operator separation controls every coefficient synthesis error. -/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H] {n : ℕ}

/-- Total error in annihilating the initial block and preserving the tail. -/
def separationError (Z : Fin n → H →L[ℂ] H) (R : H →L[ℂ] H) (k : ℕ) : ℝ :=
  ∑ j, if k ≤ j.val then ‖(ContinuousLinearMap.id ℂ H - R).comp (Z j)‖
    else ‖R.comp (Z j)‖

lemma separationError_nonneg (Z : Fin n → H →L[ℂ] H) (R : H →L[ℂ] H) (k : ℕ) :
    0 ≤ separationError Z R k := by
  apply Finset.sum_nonneg
  intro j hj
  split_ifs <;> exact norm_nonneg _

/-- Every weighted coordinate is controlled by the Euclidean coefficient
energy. This includes zero input vectors without deleting their indices. -/
lemma coefficient_mul_norm_le_energy (x : Fin n → H) (c : Fin n → ℂ) (j : Fin n) :
    ‖c j‖ * ‖x j‖ ≤ Real.sqrt (∑ l, ‖c l‖ ^ 2 * ‖x l‖ ^ 2) := by
  have hsum : 0 ≤ ∑ l, ‖c l‖ ^ 2 * ‖x l‖ ^ 2 := by positivity
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hsum, mul_pow]
  exact Finset.single_le_sum (fun l _ => mul_nonneg (sq_nonneg ‖c l‖) (sq_nonneg ‖x l‖))
    (Finset.mem_univ j)

/-- The sum of operator-norm errors bounds the synthesis error with exactly
the weighted Euclidean norm of the coefficients as a factor. -/
theorem synthesisTail_separation_error (Z : Fin n → H →L[ℂ] H)
    (R : H →L[ℂ] H) (x : Fin n → H) (c : Fin n → ℂ) (k : ℕ) {ε : ℝ}
    (herr : separationError Z R k ≤ ε) :
    ‖synthesisTail (fun j => Z j (x j)) c k -
      R (finiteSynthesis (fun j => Z j (x j)) c)‖ ≤
        ε * Real.sqrt (∑ j, ‖c j‖ ^ 2 * ‖x j‖ ^ 2) := by
  let d : Fin n → ℝ := fun j =>
    if k ≤ j.val then ‖(ContinuousLinearMap.id ℂ H - R).comp (Z j)‖ else ‖R.comp (Z j)‖
  have hd (j : Fin n) : 0 ≤ d j := by dsimp [d]; split_ifs <;> exact norm_nonneg _
  have hterm (j : Fin n) :
      ‖(if k ≤ j.val then c j • Z j (x j) else 0) - R (c j • Z j (x j))‖ ≤
        d j * (‖c j‖ * ‖x j‖) := by
    by_cases h : k ≤ j.val
    · simp only [h, ite_true, map_smul, ← smul_sub, norm_smul, d]
      have hp := mul_le_mul_of_nonneg_left
        (((ContinuousLinearMap.id ℂ H - R).comp (Z j)).le_opNorm (x j)) (norm_nonneg (c j))
      simpa only [ContinuousLinearMap.comp_apply, sub_apply,
        ContinuousLinearMap.id_apply, mul_left_comm] using hp
    · simp only [h, ite_false, zero_sub, norm_neg, map_smul, norm_smul, d]
      have hp := mul_le_mul_of_nonneg_left ((R.comp (Z j)).le_opNorm (x j)) (norm_nonneg (c j))
      simpa only [ContinuousLinearMap.comp_apply, mul_left_comm] using hp
  have hid : synthesisTail (fun j => Z j (x j)) c k -
      R (finiteSynthesis (fun j => Z j (x j)) c) =
      ∑ j, ((if k ≤ j.val then c j • Z j (x j) else 0) - R (c j • Z j (x j))) := by
    simp only [synthesisTail, finiteSynthesis, map_sum, Finset.sum_sub_distrib]
  rw [hid]
  calc
    _ ≤ ∑ j, ‖(if k ≤ j.val then c j • Z j (x j) else 0) - R (c j • Z j (x j))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, d j * Real.sqrt (∑ l, ‖c l‖ ^ 2 * ‖x l‖ ^ 2) := by
      exact Finset.sum_le_sum fun j _ => (hterm j).trans
        (mul_le_mul_of_nonneg_left (coefficient_mul_norm_le_energy x c j) (hd j))
    _ = separationError Z R k * Real.sqrt (∑ l, ‖c l‖ ^ 2 * ‖x l‖ ^ 2) := by
      rw [← Finset.sum_mul]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right herr (Real.sqrt_nonneg _)

end ProofProject
