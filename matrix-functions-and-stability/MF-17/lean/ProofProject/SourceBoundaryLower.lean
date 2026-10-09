import ProofProject.SourcePolynomialGain
import ProofProject.HilbertULift
import ProofProject.BoundaryLower

/-!
# The lower bound from the source-family boundary estimate

The concrete normalized weighted monomials have the sharp explicit
alternating gain. Their uniform adjacent-tail boundary estimate suffices for
the finite-dimensional lower bound in every fixed universe.
-/

noncomputable section

namespace ProofProject

universe u

/-- The uniform boundary estimate for the weighted monomial family implies
the finite-dimensional lower bound. -/
theorem finite_dimensional_lower_of_source_boundary {M : ℝ} (hM : 1 < M)
    (hboundary : ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n →
      HasBoundaryEstimate
        (sourceUnitFamily (growthExponent M) (growthExponent_pos hM)
          (growthExponent_mem_Ioo hM).2 : Fin n → SourceAngularL2) M B) :
    ∃ d : ℝ, 0 < d ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, t₀ ≤ t →
        HasFiniteWitness.{u} M t (d * growthLog t ^ growthExponent M) := by
  obtain ⟨B, hB, hboundary⟩ := hboundary
  obtain ⟨d, hd, hgain⟩ := sourceUnitFamily_alternating_gain
    (growthExponent_pos hM) (growthExponent_mem_Ioo hM).2
  apply finite_dimensional_lower_of_boundary_models hM
  refine ⟨B, hB, d, hd, 1, ?_⟩
  intro n hn
  let f : Fin n → SourceAngularL2 := sourceUnitFamily (growthExponent M)
    (growthExponent_pos hM) (growthExponent_mem_Ioo hM).2
  refine ⟨ULift.{u} SourceAngularL2, inferInstance, inferInstance,
    (fun i => ULift.up (f i)), ?_, ?_, ?_⟩
  · intro i
    exact sourceUnitFamily_norm (growthExponent_pos hM) (growthExponent_mem_Ioo hM).2 i
  · exact (hboundary n hn).ulift
  · simpa only [finiteSynthesis_ulift_norm] using hgain n hn

end ProofProject
