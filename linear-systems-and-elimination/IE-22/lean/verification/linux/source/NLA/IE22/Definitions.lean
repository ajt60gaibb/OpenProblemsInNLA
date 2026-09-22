import NLA.IE21.FiniteSize

/-!
UNREVIEWED IE-22 statement draft. No proof implementation is present.
IE-21 is imported unchanged; portable dependency packaging is not selected yet.
Original mathematical proof: Matthew J. Colbrook.
Formalization draft: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

/-- Literal unit Euclidean row condition. -/
def UnitRows {m n : ℕ} (A : Mat m n) : Prop :=
  ∀ i, ‖matrixRow A i‖ = 1

/-- The canonical unsquared, normalized singular statistic. -/
def normalizedSingular {m n : ℕ} (θ : ℝ) (A : Mat m n) : ℝ :=
  Real.sqrt ((n : ℝ) / m) * deletionSingular θ A

def unitRowValues (θ : ℝ) (m n : ℕ) : Set ℝ :=
  {z | ∃ A : Mat m n, UnitRows A ∧ z = normalizedSingular θ A}

/-- Literal canonical supremum M; nonempty/finite/attained semantics are compulsory. -/
def extremalValue (θ : ℝ) (m n : ℕ) : ℝ := sSup (unitRowValues θ m n)

def sharpConstant (θ : ℝ) : ℝ := Real.sqrt (gaussianTrim θ)

/-- The original two-threshold eventual-uniform property, with epsilon outside
both existential thresholds. The natural thresholds are integers. -/
def EventualUniformUpper (θ C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N R : ℕ,
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → N ≤ n → (R : ℝ) ≤ (m : ℝ) / n →
      extremalValue θ m n ≤ C + ε

/-- Actual restriction of A to an isometrically embedded Euclidean subspace. -/
def projectedMatrix {m n d : ℕ} (A : Mat m n)
    (J : Space d →ₗᵢ[ℝ] Space n) : Mat m d :=
  fun i j => inner ℝ (matrixRow A i) (J (EuclideanSpace.single j 1))

/-- The canonical threshold dual evaluated on correlated projected Gaussian rows. -/
def projectedObjective {m d : ℕ} (θ : ℝ) (B : Mat m d) (t : ℝ)
    (g : Space d) : ℝ :=
  trimDual (retainedRows θ m) (fun i => (matrixMap B g i) ^ 2) t

def projectedEnergy {m d : ℕ} (B : Mat m d) (g : Space d) : ℝ :=
  ‖matrixMap B g‖ ^ 2 / m

def gramMatrix {m d : ℕ} (B : Mat m d) : Matrix (Fin d) (Fin d) ℝ :=
  B.transpose * B

/-- The three source exceptional probabilities, with retained dimension d. -/
def projectionFailure (θ : ℝ) (d r : ℕ) (δ : ℝ) : ℝ :=
  2 / ((r : ℝ) + 1) +
    4 * truncationScale θ * (truncationScale θ / δ + 2) /
      (((r : ℝ) + 1) * δ ^ 2) +
    2 / ((d : ℝ) * δ ^ 2)

def ProjectionGood {m d : ℕ} (θ : ℝ) (B : Mat m d) (δ : ℝ) : Set (Space d) :=
  {g | projectedEnergy B g ≤ 2 ∧ (1 - δ) * (d : ℝ) ≤ ‖g‖ ^ 2 ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ truncationScale θ →
      projectedObjective θ B t g ≤ gaussianTrim θ + 2 * δ}

def deterministicFailure (θ : ℝ) (n r : ℕ) (δ : ℝ) : ℝ :=
  projectionFailure θ (n - r) r δ

/-- Exact boxed deterministic bound; n-r is positive in all stated uses. -/
def deterministicBound (θ : ℝ) (n r : ℕ) (δ : ℝ) : ℝ :=
  (n : ℝ) / (((n - r : ℕ) : ℝ) * (1 - δ)) * (gaussianTrim θ + 2 * δ)

def deletionSchedule (n : ℕ) : ℕ := ⌊Real.rpow (n : ℝ) (2 / 3 : ℝ)⌋₊
def errorSchedule (n : ℕ) : ℝ := Real.rpow (n : ℝ) (-(1 / 6 : ℝ))

end NLA.IE22
