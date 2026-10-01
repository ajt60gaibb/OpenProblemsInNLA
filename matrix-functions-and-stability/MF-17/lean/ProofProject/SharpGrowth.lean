import ProofProject.SharpUpperBound
import ProofProject.LowerBound

/-! The exact fixed-M asymptotic of the growth envelope. -/

noncomputable section

namespace ProofProject

universe u

/-- The sharp upper estimate passes to the genuine envelope using its
independently established nonempty attainable set. -/
theorem growthEnvelope_sharp_upper {M : ℝ} (hM : 1 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      growthEnvelope.{u} M t ≤ C * growthLog t ^ growthExponent M := by
  obtain ⟨C, hC, hbound⟩ := exists_inverseEvolution_sharp_upper.{u} M hM
  refine ⟨C, hC, ?_⟩
  intro t ht
  apply csSup_le (attainableNorms_nonempty M t hM.le)
  rintro r ⟨H, hN, hI, hcomp, T, B, hB, rfl⟩
  exact hbound H T B hB t ht

/-- The matching asymptotic upper and lower bounds of the source theorem. -/
theorem sharp_growth {M : ℝ} (hM : 1 < M) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧
      ∀ t : ℝ, t₀ ≤ t →
        c * growthLog t ^ growthExponent M ≤ growthEnvelope.{u} M t ∧
        growthEnvelope.{u} M t ≤ C * growthLog t ^ growthExponent M := by
  obtain ⟨c, t₀, hc, ht₀, hlower⟩ := growthEnvelope_sharp_lower.{u} hM
  obtain ⟨C, hC, hupper⟩ := growthEnvelope_sharp_upper.{u} hM
  exact ⟨c, C, t₀, hc, hC, ht₀, fun t ht =>
    ⟨hlower t ht, hupper t (ht₀.trans_le ht)⟩⟩

end ProofProject
