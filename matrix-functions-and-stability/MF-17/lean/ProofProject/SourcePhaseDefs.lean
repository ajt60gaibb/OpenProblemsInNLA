import ProofProject.SourceWeightBounds
import ProofProject.SourceWeightParameters

/-! Boundary phase quantities, defined without a global argument function. -/

noncomputable section

namespace ProofProject

def sourceCircle (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

@[simp] lemma norm_sourceCircle (θ : ℝ) : ‖sourceCircle θ‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal θ

/-- The positive inward phase correction on the upper semicircle. -/
def sourcePhaseCorrection (α θ : ℝ) : ℝ :=
  2 * (α / 4) *
    ((2 * Real.sin (θ / 2)) ^ sourceWeightNu α *
        Real.sin (sourceWeightNu α * ((Real.pi - θ) / 2)) +
      (2 * Real.cos (θ / 2)) ^ sourceWeightNu α *
        Real.sin (sourceWeightNu α * (θ / 2)))

/-- The unimodular phase ratio; analytic boundary claims omit the endpoints. -/
def sourceBoundaryPhase (α θ : ℝ) : ℂ :=
  starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) /
    sourceWeightFactor α (sourceCircle θ)

def sourcePhaseMargin (α θ : ℝ) : ℝ :=
  2 * Real.cos (Real.pi * α / 2) *
    ((sourceBoundaryPhase α θ).re - Real.cos (Real.pi * α / 2))

end ProofProject
