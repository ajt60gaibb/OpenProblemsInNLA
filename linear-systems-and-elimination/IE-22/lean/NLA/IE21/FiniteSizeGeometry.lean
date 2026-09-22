import NLA.IE21.UniformTrimmingGeometry
import NLA.IE21.RatioAlgebra
import NLA.IE21.GaussianTrimming

/-! Exact finite-size consequences of the IE-21 good event.
Original analytic argument: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology. -/
set_option autoImplicit false
noncomputable section
namespace NLA.IE21

lemma goodEvent_statistics (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (A : Mat m n)
    (t ε δ : ℝ) (ht : t < 1) (hgood : A ∈ GoodEvent θ m n t ε δ) :
    0 < operatorNorm A ∧
      |normalizedOperator A - 1| ≤ t ∧
      |normalizedDeletion θ A - gaussianTrim θ| ≤
        trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) ∧
      |deletionRatio θ A - gaussianTrim θ| ≤ finiteRatioError θ m n t ε δ := by
  have ho : |normalizedOperator A - 1| ≤ t :=
    (abs_normalizedOperator_sub_one_le_covarianceError A hn).trans hgood.1
  obtain ⟨⟨x, hx, hd⟩, _⟩ := directional_minimum θ hθ A hm hn
  have hdel : |normalizedDeletion θ A - gaussianTrim θ| ≤
      trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) := by
    simpa only [hd] using hgood.2 x hx
  have hg := gaussian_constant θ hθ
  have hr := ratio_stability (normalizedDeletion θ A) (normalizedOperator A) (gaussianTrim θ)
    (trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ))) t hg.2.2.2.2 hdel ho ht
  have hop : 0 < operatorNorm A := by
    have h0 : 0 ≤ operatorNorm A := norm_nonneg _
    by_contra h
    have hz : operatorNorm A = 0 := le_antisymm (le_of_not_gt h) h0
    have : normalizedOperator A = 0 := by simp [normalizedOperator, hz]
    linarith [hr.1]
  refine ⟨hop, ho, hdel, ?_⟩
  rw [deletionRatio_eq_normalized θ A hm hn]
  exact hr.2

end NLA.IE21
