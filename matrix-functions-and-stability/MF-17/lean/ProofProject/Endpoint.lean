import ProofProject.ScalarExamples
import ProofProject.Contractive

/-! # Exact value at the contractive endpoint -/

noncomputable section

namespace ProofProject

universe u

/-- Contractivity bounds every member of the class, including the zero space. -/
theorem contractive_attainableNorms_bddAbove {t : ℝ} (ht : 0 ≤ t) :
    BddAbove (attainableNorms.{u} 1 t) := by
  refine ⟨1, ?_⟩
  rintro r ⟨H, hN, hI, hC, T, B, hB, rfl⟩
  exact generatorInverse_evolution_norm_le_one T B hB ht

/-- The contractive endpoint, including time zero. -/
theorem contractive_envelope {t : ℝ} (ht : 0 ≤ t) :
    growthEnvelope.{u} 1 t = 1 := by
  apply le_antisymm
  · apply csSup_le (attainableNorms_nonempty 1 t le_rfl)
    rintro r ⟨H, hN, hI, hC, T, B, hB, rfl⟩
    exact generatorInverse_evolution_norm_le_one T B hB ht
  · exact one_le_growthEnvelope 1 t le_rfl (contractive_attainableNorms_bddAbove ht)

/-- At time zero every operator exponential is the identity. -/
theorem attainableNorms_zero_bddAbove (M : ℝ) :
    BddAbove (attainableNorms.{u} M 0) := by
  refine ⟨1, ?_⟩
  rintro r ⟨H, hN, hI, hC, T, B, hB, rfl⟩
  simp only [inverseEvolution, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
  exact ContinuousLinearMap.norm_id_le

/-- The normalized class has envelope exactly one at time zero. -/
theorem growthEnvelope_zero (M : ℝ) (hM : 1 ≤ M) :
    growthEnvelope.{u} M 0 = 1 := by
  apply le_antisymm
  · apply csSup_le (attainableNorms_nonempty M 0 hM)
    rintro r ⟨H, hN, hI, hC, T, B, hB, rfl⟩
    simp only [inverseEvolution, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact one_le_growthEnvelope M 0 hM (attainableNorms_zero_bddAbove M)

end ProofProject
