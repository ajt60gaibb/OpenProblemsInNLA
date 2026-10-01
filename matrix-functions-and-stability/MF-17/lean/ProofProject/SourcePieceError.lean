import ProofProject.SourcePieceResolvent
import ProofProject.BalancedSeparation

/-!
# Square-root errors for the actual source pieces

The damping is at most one at positive time. Taking square roots of the
proved deletion and retention estimates gives finite scalar sums with no
loss depending on the number of pieces.
-/

noncomputable section

namespace ProofProject

open Finset

universe u

private theorem sourcePiece_damping_le_one (q : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-sourcePieceScale q / t) ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sourcePieceScale_pos q).le) ht.le)

theorem sqrt_sourcePiece_quarter_power (q : ℕ) :
    Real.sqrt (sourcePieceScale q ^ (-1 / 4 : ℝ)) =
      sourcePieceScale q ^ (-1 / 8 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (sourcePieceScale_pos q).le]
  congr 1
  norm_num

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- No summation or sign change enters the square-root deletion bound. -/
theorem sourcePiece_sqrt_delete_le {C t r : ℝ} (hC : 0 ≤ C) (ht : 0 < t)
    (hr : 0 ≤ r) (q : ℕ) (B R : H →L[ℂ] H)
    (h : ‖R * B‖ ≤ C * Real.exp (-sourcePieceScale q / t) *
      (r / sourcePieceLambda (q + 1) + sourcePieceScale q ^ (-1 / 4 : ℝ))) :
    Real.sqrt ‖R * B‖ ≤ Real.sqrt C *
      (Real.sqrt (r / sourcePieceLambda (q + 1)) + sourcePieceScale q ^ (-1 / 8 : ℝ)) := by
  have h0 : 0 ≤ r / sourcePieceLambda (q + 1) + sourcePieceScale q ^ (-1 / 4 : ℝ) := by
    have := sourcePieceLambda_pos (q + 1)
    have := sourcePieceScale_pos q
    positivity
  have h' := h.trans (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right hC (sourcePiece_damping_le_one q ht)) h0)
  apply (Real.sqrt_le_sqrt h').trans
  rw [Real.sqrt_mul hC]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg C)
  rw [← sqrt_sourcePiece_quarter_power]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hx : 0 ≤ r / sourcePieceLambda (q + 1) :=
    div_nonneg hr (sourcePieceLambda_pos _).le
  have hy : 0 ≤ sourcePieceScale q ^ (-1 / 4 : ℝ) :=
    Real.rpow_nonneg (sourcePieceScale_pos _).le _
  rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
  nlinarith [mul_nonneg (Real.sqrt_nonneg (r / sourcePieceLambda (q + 1)))
    (Real.sqrt_nonneg (sourcePieceScale q ^ (-1 / 4 : ℝ)))]

/-- The retention bound has the opposite lambda ratio. -/
theorem sourcePiece_sqrt_keep_le {C t r : ℝ} (hC : 0 ≤ C) (ht : 0 < t)
    (hr : 0 < r) (q : ℕ) (B R : H →L[ℂ] H)
    (h : ‖(1 - R) * B‖ ≤ C * Real.exp (-sourcePieceScale q / t) * sourcePieceLambda q / r) :
    Real.sqrt ‖(1 - R) * B‖ ≤ Real.sqrt C * Real.sqrt (sourcePieceLambda q / r) := by
  have h' : ‖(1 - R) * B‖ ≤ C * (sourcePieceLambda q / r) := by
    apply h.trans
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hC (sourcePiece_damping_le_one q ht))
      (div_nonneg (sourcePieceLambda_pos q).le hr.le)
  simpa only [Real.sqrt_mul hC] using Real.sqrt_le_sqrt h'

/-- Splitting an ordered cut gives precisely two geometric sums and the
absolute-integration remainder. The hypotheses are the actual piece bounds. -/
theorem sourcePiece_sqrtSeparationError_le {n : ℕ} {C t r : ℝ}
    (hC : 0 ≤ C) (ht : 0 < t) (hr : 0 < r)
    (q : Fin n → ℕ) (B : Fin n → H →L[ℂ] H) (R : H →L[ℂ] H) (k : ℕ)
    (hdelete : ∀ j, j.val < k → ‖R * B j‖ ≤
      C * Real.exp (-sourcePieceScale (q j) / t) *
        (r / sourcePieceLambda (q j + 1) + sourcePieceScale (q j) ^ (-1 / 4 : ℝ)))
    (hkeep : ∀ j, k ≤ j.val → ‖(1 - R) * B j‖ ≤
      C * Real.exp (-sourcePieceScale (q j) / t) * sourcePieceLambda (q j) / r) :
    sqrtSeparationError B R k ≤ Real.sqrt C *
      ((∑ j ∈ univ.filter (fun j : Fin n => j.val < k), Real.sqrt (r / sourcePieceLambda (q j + 1))) +
        (∑ j ∈ univ.filter (fun j : Fin n => k ≤ j.val), Real.sqrt (sourcePieceLambda (q j) / r)) +
        ∑ j ∈ univ.filter (fun j : Fin n => j.val < k), sourcePieceScale (q j) ^ (-1 / 8 : ℝ)) := by
  classical
  have hpoint (j : Fin n) :
      Real.sqrt (if k ≤ j.val then ‖(ContinuousLinearMap.id ℂ H - R).comp (B j)‖
        else ‖R.comp (B j)‖) ≤
      Real.sqrt C * ((if j.val < k then Real.sqrt (r / sourcePieceLambda (q j + 1)) else 0) +
        (if k ≤ j.val then Real.sqrt (sourcePieceLambda (q j) / r) else 0) +
        if j.val < k then sourcePieceScale (q j) ^ (-1 / 8 : ℝ) else 0) := by
    by_cases hj : k ≤ j.val
    · simp only [hj, not_lt.mpr hj, if_true, if_false, zero_add, add_zero]
      exact sourcePiece_sqrt_keep_le hC ht hr (q j) (B j) R (hkeep j hj)
    · simp only [hj, lt_of_not_ge hj, if_true, if_false, add_zero]
      exact sourcePiece_sqrt_delete_le hC ht hr.le (q j) (B j) R
        (hdelete j (lt_of_not_ge hj))
  calc
    _ ≤ ∑ j, Real.sqrt C *
        ((if j.val < k then Real.sqrt (r / sourcePieceLambda (q j + 1)) else 0) +
          (if k ≤ j.val then Real.sqrt (sourcePieceLambda (q j) / r) else 0) +
          if j.val < k then sourcePieceScale (q j) ^ (-1 / 8 : ℝ) else 0) :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = _ := by rw [← Finset.mul_sum]; simp only [Finset.sum_add_distrib, Finset.sum_filter]

end ProofProject
