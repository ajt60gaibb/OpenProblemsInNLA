import ProofProject.SourceBoundaryEstimate
import ProofProject.SourceBoundaryLower
import ProofProject.Envelope

/-! The unconditional finite-dimensional lower bound at the exact source rate. -/

noncomputable section

namespace ProofProject

universe u

/-- The lower bound can be witnessed in finite dimensions with the same M. -/
theorem finite_dimensional_lower {M : ℝ} (hM : 1 < M) :
    ∃ c t₀ : ℝ, 0 < c ∧ 0 < t₀ ∧
      ∀ t : ℝ, t₀ ≤ t →
        HasFiniteWitness.{u} M t (c * growthLog t ^ growthExponent M) := by
  obtain ⟨c, hc, t₀, ht₀, hw⟩ := finite_dimensional_lower_of_source_boundary.{u} hM
    ⟨sourceBoundaryConstant M, sourceBoundaryConstant_pos hM,
      fun n _ => sourceUnitFamily_hasBoundaryEstimate hM n⟩
  exact ⟨c, t₀, hc, ht₀, hw⟩

/-- A finite witness gives a lower comparison with the established finite
supremum. No nonemptiness or boundedness premise is left to the caller. -/
theorem HasFiniteWitness.le_growthEnvelope {M t l : ℝ} (hM : 1 ≤ M) (ht : 0 ≤ t)
    (h : HasFiniteWitness.{u} M t l) : l ≤ growthEnvelope.{u} M t := by
  obtain ⟨H, hnorm, hip, hcomp, hfin, T, B, hB, hl⟩ := h
  exact hl.trans (le_csSup (attainableNorms_bddAbove hM ht)
    ⟨H, hnorm, hip, hcomp, T, B, hB, rfl⟩)

/-- The lower half of the sharp envelope asymptotic, with the exact exponent. -/
theorem growthEnvelope_sharp_lower {M : ℝ} (hM : 1 < M) :
    ∃ c t₀ : ℝ, 0 < c ∧ 0 < t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      c * growthLog t ^ growthExponent M ≤ growthEnvelope.{u} M t := by
  obtain ⟨c, t₀, hc, ht₀, hw⟩ := finite_dimensional_lower.{u} hM
  exact ⟨c, t₀, hc, ht₀, fun t ht =>
    (hw t ht).le_growthEnvelope hM.le (ht₀.le.trans ht)⟩

end ProofProject
