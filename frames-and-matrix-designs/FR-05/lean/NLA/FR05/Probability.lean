/-
The exact probability-space interface for the original FR-05 statement.
The standard Gaussian on the underlying real Euclidean space is scaled by
`1 / sqrt 2`, so every real and imaginary coordinate has variance `1 / 2`.
Measurability of the injectivity event and the quantitative estimates remain
separate proof obligations.
-/
import NLA.FR05.Definitions
import Mathlib.Probability.Distributions.Gaussian.Multivariate

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NLA.FR05

/-- Product measurable space on finite complex matrices. -/
noncomputable instance frameMeasurableSpace (m d : ℕ) : MeasurableSpace (Frame m d) :=
  @MeasurableSpace.pi (Fin m) (fun _ : Fin m ↦ Fin d → ℂ)
    (fun _ ↦ @MeasurableSpace.pi (Fin d) (fun _ : Fin d ↦ ℂ)
      (fun _ ↦ Complex.measurableSpace))

/-- Real coordinates for a complex `m × d` frame. -/
abbrev RealFrameCoordinates (m d : ℕ) := EuclideanSpace ℝ ((Fin m × Fin d) × Fin 2)

/-- The real/imaginary coordinate identification of a complex frame. -/
def realCoordinatesToComplexFrame {m d : ℕ}
    (x : RealFrameCoordinates m d) : Frame m d :=
  fun i j ↦ (x ((i, j), 0) : ℂ) + (x ((i, j), 1) : ℂ) * Complex.I

@[fun_prop]
theorem measurable_realCoordinatesToComplexFrame {m d : ℕ} :
    Measurable (realCoordinatesToComplexFrame (m := m) (d := d)) := by
  unfold realCoordinatesToComplexFrame
  fun_prop

/-- The iid standard complex-Gaussian law on `m × d` frames, represented as a
real Gaussian on the finite-dimensional complex matrix space and scaled so
that the real and imaginary parts have variance `1/2`. -/
def standardComplexGaussianFrame (m d : ℕ) : Measure (Frame m d) :=
  (stdGaussian (RealFrameCoordinates m d)).map
    (fun x ↦ ((Real.sqrt 2)⁻¹ : ℝ) • realCoordinatesToComplexFrame x)

theorem measurable_standardComplexGaussianFrame_map (m d : ℕ) :
    Measurable (fun x : RealFrameCoordinates m d ↦
      ((Real.sqrt 2)⁻¹ : ℝ) • realCoordinatesToComplexFrame x) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  change Measurable (fun x : RealFrameCoordinates m d ↦
    ((Real.sqrt 2)⁻¹ : ℝ) •
      (((x ((i, j), 0) : ℝ) : ℂ) + ((x ((i, j), 1) : ℝ) : ℂ) * Complex.I))
  fun_prop

instance (m d : ℕ) : IsProbabilityMeasure (standardComplexGaussianFrame m d) :=
  Measure.isProbabilityMeasure_map
    (measurable_standardComplexGaussianFrame_map m d).aemeasurable

/-- The original all-signal injectivity event at the FR-05 row count. -/
def phaseRetrievalInjectivityEvent (d : ℕ) : Set (Frame (4 * d - 5) d) :=
  {A | PhaseRetrievalInjective A}

/-- The quantity called `p_d` in FR-05, using the original complex Gaussian
law and the original phase-retrieval predicate. -/
def phaseRetrievalProbability (d : ℕ) : ℝ :=
  ENNReal.toReal <|
    standardComplexGaussianFrame (4 * d - 5) d (phaseRetrievalInjectivityEvent d)

theorem phaseRetrievalProbability_nonneg (d : ℕ) :
    0 ≤ phaseRetrievalProbability d :=
  ENNReal.toReal_nonneg

/-- Even before measurability of the injectivity event is established, its
outer measure is at most one under the probability law. -/
theorem phaseRetrievalProbability_le_one (d : ℕ) :
    phaseRetrievalProbability d ≤ 1 := by
  unfold phaseRetrievalProbability
  apply ENNReal.toReal_le_of_le_ofReal zero_le_one
  simpa using
    (prob_le_one (μ := standardComplexGaussianFrame (4 * d - 5) d)
      (s := phaseRetrievalInjectivityEvent d))

end NLA.FR05
