import Target
import GraphLower
import VaryingUpper

open MeasureTheory Filter unitInterval
open scoped Topology

namespace MD01FullBridge

noncomputable def normalizedTheta (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  MD01Scratch.theta G / Real.sqrt n

private theorem normalizedTheta_measurable (n : ℕ) :
    Measurable (normalizedTheta n) := by
  exact measurable_of_finite _

/-- A graph-specific conditional upper bridge to the precise MD-01 statement.
The convergence and uniform moment hypotheses must still be established. -/
theorem sharpThetaExpectation_of_prob_and_L2
    (hL2 : ∃ C : NNReal, ∀ n,
      eLpNorm (normalizedTheta n) 2 (graphMeasure n) ≤ C)
    (hconv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => graphMeasure n
        {G : SimpleGraph (Fin n) | ε ≤ |normalizedTheta n G - 1|})
        atTop (𝓝 0)) :
    MD01Scratch.sharpThetaExpectation := by
  have hp : ∀ n, IsProbabilityMeasure (graphMeasure n) := by
    intro n
    infer_instance
  have h := varying_expectation_of_L2_and_probability
    (fun n => SimpleGraph (Fin n)) graphMeasure normalizedTheta hp
    normalizedTheta_measurable hL2 hconv
  unfold MD01Scratch.sharpThetaExpectation at *
  convert h using 1
  funext n
  simp [normalizedTheta, graphMeasure, half, integral_div]

#print axioms normalizedTheta_measurable
#print axioms sharpThetaExpectation_of_prob_and_L2

end MD01FullBridge
