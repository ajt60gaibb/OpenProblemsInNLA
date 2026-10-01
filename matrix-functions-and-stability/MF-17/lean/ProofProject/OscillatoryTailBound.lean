import ProofProject.SourcePieceTimeBound
import ProofProject.SourcePieceLimit

/-!
# The actual signed oscillatory tail satisfies the sharp growth rate

Strong convergence of the exact source-piece telescope transfers its uniform
partial-sum bound to the genuine strong-integral operator. No operator-valued
integration, representation of the inverse exponential, or Bessel asymptotic
is assumed in this theorem.
-/

noncomputable section

namespace ProofProject

open Filter

universe u

/-- The full oscillatory tail has the exact fixed-M growth exponent and clock,
uniformly over Hilbert spaces and both phase signs. -/
theorem exists_sourceOscillatoryTail_growth_bound :
    ∀ M : ℝ, 1 < M → ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (S : BoundedSemigroup M H) (t : ℝ) (ht : 0 < t),
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
        ‖S.sourceOscillatoryTailOperator t σ ht‖ ≤ C * growthLog t ^ growthExponent M := by
  intro M hM
  obtain ⟨C, hC, hbound⟩ := exists_sourcePiece_partial_sum_growth_bound.{u} M hM
  refine ⟨C, hC, ?_⟩
  intro H _ _ _ S t ht σ hσ
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hC.le (Real.rpow_nonneg (growthLog_pos ht.le).le _))
  intro x
  apply le_of_tendsto (S.tendsto_sum_sourcePieceOperator t σ ht x).norm
  exact Filter.Eventually.of_forall fun m =>
    (ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right (hbound H S t ht σ hσ m) (norm_nonneg x))

end ProofProject
