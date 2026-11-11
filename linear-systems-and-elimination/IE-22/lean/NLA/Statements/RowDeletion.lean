import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Algebra.Order.Floor.Ring

/-! Concrete shared row-deletion quantities and actual uniform spherical rows.
No assumed law record, arbitrary spectral norm, or target theorem is used. -/
set_option autoImplicit false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace NLA.Statements.RowDeletion

def UnitVector {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∑ j, (x j) ^ 2 = 1

def UnitRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i, ∑ j, (A i j) ^ 2 = 1

def RowValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  ∑ j, A i j * x j

noncomputable def RetainedCount (θ : ℝ) (m : ℕ) : ℕ :=
  Nat.floor (θ * (m : ℝ))

/-- Infimum of nonnegative energy over every retained row set and unit vector.
On the target domain the set is nonempty and its minimum is attained. -/
noncomputable def SubsingularSquared {m n : ℕ} (θ : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sInf {y : ℝ | ∃ S : Finset (Fin m), S.card = RetainedCount θ m ∧
    ∃ x : Fin n → ℝ, UnitVector x ∧ y = ∑ i ∈ S, (RowValue A i x) ^ 2}

/-- The squared Euclidean induced operator norm, on the full unit sphere. -/
noncomputable def OperatorSquared {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x : Fin n → ℝ, UnitVector x ∧
    y = ∑ i, (RowValue A i x) ^ 2}

abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- Actual normalized Euclidean surface measure. For positive n the Haar
sphere mass is finite and nonzero, including the two-point sphere for n=1. -/
noncomputable def UniformSphere (n : ℕ) : Measure (Sphere n) :=
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  (μ Set.univ)⁻¹ • μ

/-- The full independent product of the identical uniform row laws. -/
noncomputable def MatrixLaw (m n : ℕ) : Measure (Fin m → Sphere n) :=
  Measure.pi (fun _ : Fin m => UniformSphere n)

def SampleMatrix {m n : ℕ} (ω : Fin m → Sphere n) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => WithLp.ofLp (ω i).val j

def GaussianQuantile (θ a : ℝ) : Prop :=
  (gaussianReal 0 1) (Set.Icc (-a) a) = ENNReal.ofReal θ

noncomputable def TrimmedMoment (a : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) *
    ∫ t in (-a)..a, t ^ 2 * Real.exp (-(t ^ 2) / 2)

end NLA.Statements.RowDeletion
