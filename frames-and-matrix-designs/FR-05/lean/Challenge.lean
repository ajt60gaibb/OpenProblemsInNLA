import NLA.FR05.Probability

/-!
Development statement-comparison boundary, pending independent review.
The placeholders below are intentionally isolated: `Solution` and all its
dependencies do not import this module. Their corresponding declarations
are proved in `Solution`, including the unconditional FR-05 probability bound.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Topology

namespace NLA.FR05

theorem explicit_noninjective_frame (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : Frame (4 * d - 5) d, ¬ PhaseRetrievalInjective A := by
  sorry

/-- The exact quantitative target from Li's Theorem 1.4; the corresponding
declaration in `Solution` is proved without analytic hypotheses. -/
theorem phaseRetrieval_injective_probability_le_inv :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      phaseRetrievalProbability d ≤ C / d := by
  sorry

/-- The original FR-05 limit, also proved in `Solution`. -/
theorem phaseRetrieval_injective_probability_tendsto_zero :
    Filter.Tendsto phaseRetrievalProbability Filter.atTop (𝓝 0) := by
  sorry

/-- The exact algebraic reduction at the end of Proposition 3.2.
`Solution` also imports the proved source-specific likelihood estimates. -/
theorem likelihood_l2_bound_of_second_moment_estimates
    {Ω : ℕ → Type*} [∀ M, MeasurableSpace (Ω M)]
    (μ : ∀ M, Measure (Ω M)) (Lg Lr : ∀ M, Ω M → ℝ)
    (D : ℕ) (C : ℝ)
    (hcomparisons : ∀ M : ℕ, D ≤ M →
      Integrable (fun ω ↦ Lg M ω * Lg M ω) (μ M) ∧
      Integrable (fun ω ↦ Lr M ω * Lr M ω) (μ M) ∧
      Integrable (fun ω ↦ Lg M ω * Lr M ω) (μ M) ∧
      |(∫ ω, Lg M ω * Lg M ω ∂μ M) -
        (∫ ω, Lr M ω * Lr M ω ∂μ M)| ≤ C / M ∧
      |(∫ ω, Lg M ω * Lr M ω ∂μ M) -
        (∫ ω, Lr M ω * Lr M ω ∂μ M)| ≤ C / M) :
    ∀ M : ℕ, D ≤ M →
      (∫ ω, (Lg M ω - Lr M ω) ^ 2 ∂μ M) ≤ 3 * C / M := by
  sorry

end NLA.FR05
