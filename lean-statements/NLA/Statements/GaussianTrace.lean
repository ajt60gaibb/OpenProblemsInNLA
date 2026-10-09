import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gamma

/-! Concrete shared meanings for the Gaussian trace-estimation questions.
No probability, norm, or distribution is an assumed semantic parameter.
These definitions establish no tail comparison. -/
set_option autoImplicit false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace NLA.Statements.GaussianTrace

def Symmetric {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, A i j = A j i

def NonnegativeQuadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, x i * A i j * x j

def Trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, A i i

/-- The Euclidean induced operator norm, expressed on the Euclidean unit sphere.
For positive finite dimension this is the supremum of `‖A x‖₂` over `‖x‖₂=1`.
The finite-dimensional unit sphere is nonempty and the displayed set is bounded;
no empty/unbounded real-supremum convention occurs in either target. -/
noncomputable def SpectralNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x : Fin n → ℝ,
    (∑ i, (x i) ^ 2) = 1 ∧
    y = Real.sqrt (∑ i, (∑ j, A i j * x j) ^ 2)}

/-- Exact Frobenius norm, with the nonnegative square root. -/
noncomputable def FrobeniusNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)

/-- One independent standard real Gaussian for each sample/coordinate pair.
`gaussianReal` takes mean and variance, here exactly zero and one.
`Measure.pi` is the joint finite product law, not a marginal-law hypothesis. -/
noncomputable def GaussianLaw (m n : ℕ) : Measure ((Fin m × Fin n) → ℝ) :=
  Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1)

/-- The complete Gaussian trace estimator in the matrix's own dimension. -/
noncomputable def Estimator {n : ℕ} (m : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (z : (Fin m × Fin n) → ℝ) : ℝ :=
  (∑ j : Fin m, ∑ p : Fin n, ∑ q : Fin n,
    z (j, p) * A p q * z (j, q)) / (m : ℝ)

/-- Mathlib's concrete Gamma measure uses shape followed by rate:
`volume.withDensity (ofReal (β^α / Γ(α) * x^(α-1) * exp (-(β*x))))`
on nonnegative x, zero on negative x. Its density value at x=0 differs from
the source's strict-positive branch only on a Lebesgue-null singleton.
For positive shape and rate it is a probability measure, by the pinned
`isProbabilityMeasure_gammaMeasure`; no scale/rate swap is made. -/
noncomputable def GammaLaw (shape rate : ℝ) : Measure ℝ :=
  gammaMeasure shape rate

end NLA.Statements.GaussianTrace
