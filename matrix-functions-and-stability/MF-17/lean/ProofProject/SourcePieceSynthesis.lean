import ProofProject.SourcePieceSeparation
import ProofProject.SeparatorBudget
import ProofProject.SeparatedOperatorSum

/-!
# Exact-exponent synthesis of retained source pieces

The same removal index works before the Hilbert space, time, sign, and retained
family are chosen. The factor `sqrt (M+1)` is included in the error budget.
-/

noncomputable section

namespace ProofProject

universe u

/-- A logarithmic initial removal supplies the sharp bound for every retained
family with gaps at least two. Both constants precede all finite families. -/
theorem exists_sourcePiece_retained_bounds :
    ∀ M : ℝ, 1 < M → ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ m : ℕ, 1 ≤ m → ∃ J : ℕ, (J : ℝ) ≤ C * Real.log ((m : ℝ) + 2) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (S : BoundedSemigroup M H) (t : ℝ), 0 < t →
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ n : ℕ, n ≤ m →
      ∀ q : Fin n → ℕ, (∀ i j, i < j → q i + 2 ≤ q j) → (∀ j, J ≤ q j) →
        ‖∑ j, S.sourcePieceOperator (q j) t σ‖ ≤ D * (m : ℝ) ^ growthExponent M := by
  intro M hM
  have hM0 : 0 < M := by linarith
  obtain ⟨A, hA, hpiece⟩ := exists_sourcePieceOperator_bound.{u}
  obtain ⟨E, hE, hsep⟩ := exists_sourcePiece_separators.{u} M hM.le
  have hc : 0 < Real.log 16 / 18 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨C, hC, hbudget⟩ := exists_separatorRemoval_budget
    (T := Real.sqrt (M + 1) * E) hc (by positivity)
  let D₀ : ℝ := A * M ^ 3
  let G : ℝ := ((16 * Real.exp 2) * (M + 1) ^ 2 *
    Real.exp (growthExponentLipschitzConstant M)) * (D₀ + 1)
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨C, G, hC, hG, ?_⟩
  intro m hm
  obtain ⟨J, hJ, hb⟩ := hbudget m hm
  refine ⟨J, hJ, ?_⟩
  intro H _ _ _ S t ht σ hσ n hnm q hgap hqJ
  have hB (j : Fin n) : ‖S.sourcePieceOperator (q j) t σ‖ ≤ D₀ := by
    apply (hpiece H M S (q j) t ht σ hσ).trans
    apply mul_le_of_le_one_right hD₀.le
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sourcePieceScale_pos _).le) ht.le)
  apply separated_operator_sum_norm_le_of_length_le hM hD₀.le hm hnm
    (fun j => S.sourcePieceOperator (q j) t σ) hB
  intro k hk0 hkn
  obtain ⟨R, hR, hcomm, herr⟩ := hsep H S n q hgap J hqJ t ht σ hσ k hk0 hkn
  refine ⟨R, hR, hcomm, ?_⟩
  calc
    _ ≤ Real.sqrt (M + 1) * (E * sourceSeparatorDecay J) :=
      mul_le_mul_of_nonneg_left herr (Real.sqrt_nonneg _)
    _ = (Real.sqrt (M + 1) * E) * Real.exp (-(Real.log 16 / 18) * (4 / 3 : ℝ) ^ J) := by
      rw [sourceSeparatorDecay]; ring
    _ ≤ _ := hb

end ProofProject
