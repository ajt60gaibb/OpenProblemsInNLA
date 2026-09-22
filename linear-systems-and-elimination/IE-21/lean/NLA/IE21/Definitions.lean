import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
IE-21 statement draft. These definitions contain no resolution or assumed
probabilistic/spectral facts. Required semantic bridges are in Challenge.
The source proof is by Matthew J. Colbrook. Formalization draft: George
Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology

namespace NLA.IE21

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev Sphere (n : ℕ) := Metric.sphere (0 : Space n) 1

instance matrixMeasurableSpace (m n : ℕ) : MeasurableSpace (Mat m n) :=
  inferInstanceAs (MeasurableSpace (Fin m → Fin n → ℝ))

instance matrixBorelSpace (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

/-- Actual Euclidean surface measure, obtained from Euclidean Lebesgue measure. -/
def surfaceMeasure (n : ℕ) : Measure (Sphere n) :=
  (volume : Measure (Space n)).toSphere

/-- Normalization is literal inverse total mass, with no probability axiom. -/
def surfaceLaw (n : ℕ) : Measure (Sphere n) :=
  (surfaceMeasure n Set.univ)⁻¹ • surfaceMeasure n

/-- Ambient-space law of a uniform unit vector. -/
def sphereLaw (n : ℕ) : Measure (Space n) :=
  (surfaceLaw n).map Subtype.val

def rowsMatrix {m n : ℕ} (u : Fin m → Space n) : Mat m n :=
  fun i j => u i j

def matrixRow {m n : ℕ} (A : Mat m n) (i : Fin m) : Space n :=
  WithLp.toLp 2 (A i)

/-- Independent normalized surface-measure rows; no Gaussian surrogate. -/
def matrixLaw (m n : ℕ) : Measure (Mat m n) :=
  (Measure.pi (fun _ : Fin m => sphereLaw n)).map rowsMatrix

def matrixMap {m n : ℕ} (A : Mat m n) : Space n →L[ℝ] Space m :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

def operatorNorm {m n : ℕ} (A : Mat m n) : ℝ := ‖matrixMap A‖

def retainedRows (θ : ℝ) (m : ℕ) : ℕ := ⌊θ * (m : ℝ)⌋₊

def retainedMatrix {m n : ℕ} (A : Mat m n) (S : Finset (Fin m)) :
    Matrix S (Fin n) ℝ := fun i j => A i.val j

def retainedNorm {m n : ℕ} (A : Mat m n) (S : Finset (Fin m))
    (x : Space n) : ℝ := ‖Matrix.toEuclideanLin (retainedMatrix A S) x‖

/-- Infimum over the exact canonical pairs. Mandatory attainment and lower-bound
theorems rule out reliance on any empty-set/default behavior of real `sInf`. -/
def deletionSingular {m n : ℕ} (θ : ℝ) (A : Mat m n) : ℝ :=
  sInf {z | ∃ (S : Finset (Fin m)) (x : Space n),
    S.card = retainedRows θ m ∧ ‖x‖ = 1 ∧ z = retainedNorm A S x}

def finiteTrim {m : ℕ} (k : ℕ) (y : Fin m → ℝ) : ℝ :=
  sInf {z | ∃ S : Finset (Fin m), S.card = k ∧ z = ∑ i ∈ S, y i}

def trimDual {m : ℕ} (k : ℕ) (y : Fin m → ℝ) (t : ℝ) : ℝ :=
  (k : ℝ) / m * t - (1 / (m : ℝ)) * ∑ i, max (t - y i) 0

def directionalTrim {m n : ℕ} (θ : ℝ) (A : Mat m n) (x : Space n) : ℝ :=
  (n : ℝ) / m * finiteTrim (retainedRows θ m) (fun i => (matrixMap A x i) ^ 2)

def normalizedDeletion {m n : ℕ} (θ : ℝ) (A : Mat m n) : ℝ :=
  (n : ℝ) / m * deletionSingular θ A ^ 2

def normalizedOperator {m n : ℕ} (A : Mat m n) : ℝ :=
  (n : ℝ) / m * operatorNorm A ^ 2

def deletionRatio {m n : ℕ} (θ : ℝ) (A : Mat m n) : ℝ :=
  deletionSingular θ A ^ 2 / operatorNorm A ^ 2

def covarianceError {m n : ℕ} (A : Mat m n) : ℝ :=
  ‖((n : ℝ) / m) • ((matrixMap A).adjoint.comp (matrixMap A)) -
    ContinuousLinearMap.id ℝ (Space n)‖

def gaussianCutoff (θ : ℝ) : ℝ :=
  sInf {a : ℝ | 0 ≤ a ∧ θ ≤ (gaussianReal 0 1).real {g | |g| ≤ a}}

/-- Exact canonical Gaussian integral; its quantile semantics must be proved. -/
def gaussianTrim (θ : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) *
    ∫ g in Set.Icc (-gaussianCutoff θ) (gaussianCutoff θ),
      g ^ 2 * Real.exp (-(g ^ 2) / 2)

/-- The dual lower-tail functional; no unproved quantile or coupling axiom. -/
def populationTrim {Ω : Type*} [MeasurableSpace Ω]
    (θ : ℝ) (μ : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  sSup {z | ∃ t : ℝ, 0 ≤ t ∧ z = θ * t - ∫ ω, max (t - Y ω) 0 ∂μ}

def directionalEnergy {n : ℕ} (x u : Space n) : ℝ :=
  (n : ℝ) * (inner ℝ u x) ^ 2

/-- At zero the value is zero; Gaussian nullity of this case is a required bridge. -/
def gaussianDirection {n : ℕ} (g : Space n) : Space n := ‖g‖⁻¹ • g

def truncationScale (θ : ℝ) : ℝ := 2 / (1 - θ)

def trimmingError (θ : ℝ) (m : ℕ) (t ε δ : ℝ) : ℝ :=
  2 * truncationScale θ * ε + truncationScale θ / m + 2 * (1 + t) * δ

def finiteFailure (m n : ℕ) (t ε δ : ℝ) : ℝ :=
  2 * (9 : ℝ) ^ n * Real.exp (-(m : ℝ) * t ^ 2 / 512) +
  5 * (1 + 2 / δ) ^ n * Real.exp (-2 * (m : ℝ) * ε ^ 2)

def finiteRatioError (θ : ℝ) (m n : ℕ) (t ε δ : ℝ) : ℝ :=
  (trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) + t) / (1 - t)

def aspectParameter (m n : ℕ) : ℝ :=
  32 * Real.sqrt (Real.log ((m : ℝ) / n) / ((m : ℝ) / n))

def GoodEvent (θ : ℝ) (m n : ℕ) (t ε δ : ℝ) : Set (Mat m n) :=
  {A | covarianceError A ≤ t ∧ ∀ x : Space n, ‖x‖ = 1 →
    |directionalTrim θ A x - gaussianTrim θ| ≤
      trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ))}

/-- Independent rows with the actual normalized surface law on any probability space. -/
def IndependentSphereRows {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (μ : Measure Ω) (A : Ω → Mat m n) : Prop :=
  Measurable A ∧
    iIndepFun (fun i ω => matrixRow (A ω) i) μ ∧
    ∀ i, μ.map (fun ω => matrixRow (A ω) i) = sphereLaw n

end NLA.IE21
