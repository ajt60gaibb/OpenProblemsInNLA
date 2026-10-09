import ProofProject.SourcePieceSynthesis
import ProofProject.FiniteParitySplit

/-!
# Sharp finite sums of the actual oscillatory source pieces

The logarithmic initial segment and the two retained parity classes together
cost exactly the target power of the number of pieces. All source separator
premises are discharged.
-/

noncomputable section

namespace ProofProject

open Finset

universe u

/-- Every finite initial sum of source pieces satisfies the sharp power bound,
uniformly over positive times, both signs and all complete complex Hilbert
spaces in the fixed arbitrary universe. Empty sums are included. -/
theorem exists_sourcePiece_finite_sum_bound :
    ∀ M : ℝ, 1 < M → ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (S : BoundedSemigroup M H) (t : ℝ), 0 < t →
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ m : ℕ,
        ‖∑ q ∈ range m, S.sourcePieceOperator q t σ‖ ≤ C * (m : ℝ) ^ growthExponent M := by
  intro M hM
  have hM0 : 0 < M := by linarith
  obtain ⟨A, hA, hpiece⟩ := exists_sourcePieceOperator_bound.{u}
  obtain ⟨K, D, hK, hD, hretained⟩ := exists_sourcePiece_retained_bounds.{u} M hM
  obtain ⟨L, hL, hlog⟩ := exists_log_add_two_le_rpow (growthExponent_pos hM)
  let D₀ : ℝ := A * M ^ 3
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  refine ⟨K * D₀ * L + 2 * D, by positivity, ?_⟩
  intro H _ _ _ S t ht σ hσ m
  by_cases hm0 : m = 0
  · subst m
    simp only [range_zero, sum_empty, norm_zero]
    positivity
  have hm : 1 ≤ m := by omega
  obtain ⟨J, hJ, hretain⟩ := hretained m hm
  have hB (q : ℕ) : ‖S.sourcePieceOperator q t σ‖ ≤ D₀ := by
    apply (hpiece H M S q t ht σ hσ).trans
    apply mul_le_of_le_one_right hD₀.le
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sourcePieceScale_pos _).le) ht.le)
  have hp (p : ℕ) :
      ‖∑ q ∈ (range m).filter (fun q => J ≤ q ∧ q % 2 = p), S.sourcePieceOperator q t σ‖ ≤
        D * (m : ℝ) ^ growthExponent M := by
    let s := (range m).filter (fun q => J ≤ q ∧ q % 2 = p)
    let q := s.orderEmbOfFin rfl
    have hcard : s.card ≤ m := (card_filter_le _ _).trans_eq (card_range m)
    have hgap : ∀ i j, i < j → q i + 2 ≤ q j := by
      intro i j hij
      exact orderEmbOfFin_add_two_le
        (fun a ha => (mem_filter.mp ha).2.2) hij
    have hlow : ∀ j, J ≤ q j := by
      intro j
      exact (mem_filter.mp (s.orderEmbOfFin_mem rfl j)).2.1
    have h := hretain H S t ht σ hσ s.card hcard q hgap hlow
    dsimp only [q] at h
    rw [sum_orderEmbOfFin_eq s (fun a => S.sourcePieceOperator a t σ)] at h
    exact h
  calc
    _ ≤ (J : ℝ) * D₀ +
        ‖∑ q ∈ (range m).filter (fun q => J ≤ q ∧ q % 2 = 0), S.sourcePieceOperator q t σ‖ +
        ‖∑ q ∈ (range m).filter (fun q => J ≤ q ∧ q % 2 = 1), S.sourcePieceOperator q t σ‖ :=
      norm_sum_range_le_initial_add_parity _ hD₀.le hB J m
    _ ≤ (J : ℝ) * D₀ + D * (m : ℝ) ^ growthExponent M + D * (m : ℝ) ^ growthExponent M :=
      add_le_add (add_le_add_right (hp 0) _) (hp 1)
    _ ≤ (K * Real.log ((m : ℝ) + 2)) * D₀ +
        D * (m : ℝ) ^ growthExponent M + D * (m : ℝ) ^ growthExponent M := by
      gcongr
    _ ≤ (K * (L * (m : ℝ) ^ growthExponent M)) * D₀ +
        D * (m : ℝ) ^ growthExponent M + D * (m : ℝ) ^ growthExponent M := by
      gcongr
      exact hlog m hm
    _ = _ := by ring

end ProofProject
