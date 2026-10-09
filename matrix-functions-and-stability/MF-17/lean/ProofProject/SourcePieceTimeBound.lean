import ProofProject.SourcePieceFiniteSum
import ProofProject.SourcePieceClock
import ProofProject.SourcePieceDampedTail

/-!
# The growth clock controls every partial source-piece sum

The exact-exponent finite synthesis handles pieces before the clock index.
The exponentially damped remainder has a bounded finite absolute sum, even
when the requested partial sum ends before that index.
-/

noncomputable section

namespace ProofProject

open Finset

universe u

theorem exists_sourcePiece_partial_sum_growth_bound :
    ∀ M : ℝ, 1 < M → ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (S : BoundedSemigroup M H) (t : ℝ), 0 < t →
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ m : ℕ,
        ‖∑ q ∈ range m, S.sourcePieceOperator q t σ‖ ≤
          C * growthLog t ^ growthExponent M := by
  intro M hM
  have hM0 : 0 < M := by linarith
  obtain ⟨A, hA, hpiece⟩ := exists_sourcePieceOperator_bound.{u}
  obtain ⟨F, hF, hfinite⟩ := exists_sourcePiece_finite_sum_bound.{u} M hM
  let D : ℝ := A * M ^ 3
  have hD : 0 < D := by dsimp [D]; positivity
  let G : ℝ := F * sourcePieceClockConstant ^ growthExponent M
  have hG : 0 < G := mul_pos hF
    (Real.rpow_pos_of_pos sourcePieceClockConstant_pos _)
  refine ⟨G + D, by positivity, ?_⟩
  intro H _ _ _ S t ht σ hσ m
  let k := sourcePieceClockIndex t
  have hpow : 1 ≤ growthLog t ^ growthExponent M :=
    Real.one_le_rpow (one_le_growthLog ht.le) (growthExponent_nonneg M)
  have hprefix (j : ℕ) (hj : j ≤ k) :
      ‖∑ q ∈ range j, S.sourcePieceOperator q t σ‖ ≤ G * growthLog t ^ growthExponent M := by
    apply (hfinite H S t ht σ hσ j).trans
    calc
      _ ≤ F * (sourcePieceClockConstant * growthLog t) ^ growthExponent M := by
        apply mul_le_mul_of_nonneg_left _ hF.le
        apply Real.rpow_le_rpow (Nat.cast_nonneg j) _ (growthExponent_nonneg M)
        exact (show (j : ℝ) ≤ k by exact_mod_cast hj).trans (sourcePieceClockIndex_le ht)
      _ = _ := by rw [Real.mul_rpow sourcePieceClockConstant_pos.le (growthLog_pos ht.le).le]; dsimp [G]; ring
  have htail : ‖∑ q ∈ Ico k m, S.sourcePieceOperator q t σ‖ ≤ D := by
    calc
      _ ≤ ∑ q ∈ Ico k m, ‖S.sourcePieceOperator q t σ‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Ico k m, D * Real.exp (-sourcePieceScale q / t) :=
        sum_le_sum fun q _ => hpiece H M S q t ht σ hσ
      _ = D * ∑ q ∈ Ico k m, Real.exp (-sourcePieceScale q / t) := by rw [mul_sum]
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left
        (sum_sourcePiece_damping_Ico_le_one k m ht (sourcePieceClockIndex_time_le_scale ht)) hD.le
      _ = D := mul_one D
  by_cases hm : m ≤ k
  · exact (hprefix m hm).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le)
      (Real.rpow_nonneg (growthLog_pos ht.le).le _))
  · have hkm : k ≤ m := by omega
    rw [← sum_range_add_sum_Ico (fun q => S.sourcePieceOperator q t σ) hkm]
    calc
      _ ≤ ‖∑ q ∈ range k, S.sourcePieceOperator q t σ‖ +
          ‖∑ q ∈ Ico k m, S.sourcePieceOperator q t σ‖ := norm_add_le _ _
      _ ≤ G * growthLog t ^ growthExponent M + D := add_le_add (hprefix k le_rfl) htail
      _ ≤ (G + D) * growthLog t ^ growthExponent M := by nlinarith

end ProofProject
