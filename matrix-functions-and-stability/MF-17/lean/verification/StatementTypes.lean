import Solution

/-! Direct checks of all five independent target types in a Solution-only environment. -/

noncomputable section
namespace ProofProject
universe u

example {M : ℝ} (hM : 1 ≤ M)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : StableSemigroup M H) : ∃! B : H →L[ℂ] H, IsGeneratorInverse T B := by
  exact ProofProject.stableSemigroup_hasGeneratorInverse hM T

example {M t : ℝ} (hM : 1 ≤ M) (ht : 0 ≤ t) :
    BddAbove (attainableNorms.{u} M t) := by
  exact ProofProject.attainableNorms_bddAbove hM ht

example {M : ℝ} (hM : 1 < M) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧
      ∀ t : ℝ, t₀ ≤ t →
        c * growthLog t ^ growthExponent M ≤ growthEnvelope.{u} M t ∧
        growthEnvelope.{u} M t ≤ C * growthLog t ^ growthExponent M := by
  exact ProofProject.sharp_growth hM

example {M : ℝ} (hM : 1 < M) :
    ∃ c t₀ : ℝ, 0 < c ∧ 0 < t₀ ∧
      ∀ t : ℝ, t₀ ≤ t →
        HasFiniteWitness.{u} M t (c * growthLog t ^ growthExponent M) := by
  exact ProofProject.finite_dimensional_lower hM

example {t : ℝ} (ht : 0 ≤ t) :
    growthEnvelope.{u} 1 t = 1 := by
  exact ProofProject.contractive_envelope ht

end ProofProject
