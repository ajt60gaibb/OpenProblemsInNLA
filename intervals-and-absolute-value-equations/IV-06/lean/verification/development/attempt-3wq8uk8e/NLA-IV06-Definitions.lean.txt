import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.Real
import Mathlib.SetTheory.Cardinal.Order

/-!
# IV-06: the original interval-eigenvalue component bound

The counterexample and its exact data are Matthew J. Colbrook's. Formalization:
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA; AI-assisted.

These definitions contain no theorem assumptions or replacement definition holes.
The interval family has all entries independent. Components are Mathlib's actual
connected-component quotient of the attained set with its real subspace topology.
-/

noncomputable section

namespace NLA.IV06

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Entrywise order, without imposing symmetry or coupling distinct entries. -/
def EntrywiseLE {n : ℕ} (L U : RealMatrix n) : Prop :=
  ∀ i j, L i j ≤ U i j

/-- The entire independent-entry closed interval family; fixed entries are allowed. -/
def InIntervalFamily {n : ℕ} (L U A : RealMatrix n) : Prop :=
  EntrywiseLE L A ∧ EntrywiseLE A U

/-- A real eigenvalue means an actual nonzero real eigenvector. -/
def HasRealEigenvalue {n : ℕ} (A : RealMatrix n) (lam : ℝ) : Prop :=
  ∃ v : Fin n → ℝ, v ≠ 0 ∧ A.mulVec v = lam • v

/-- The union of the real eigenvalues of every admissible matrix. -/
def realEigenvalueSet {n : ℕ} (L U : RealMatrix n) : Set ℝ :=
  {lam | ∃ A : RealMatrix n, InIntervalFamily L U A ∧ HasRealEigenvalue A lam}

/-- Actual characteristic determinant, with convention det(lam I - A). -/
def characteristicDet {n : ℕ} (A : RealMatrix n) (lam : ℝ) : ℝ :=
  Matrix.det (lam • (1 : RealMatrix n) - A)

/-- Cardinality is used, so infinite component spaces cannot count as zero. -/
def componentCard (S : Set ℝ) : Cardinal :=
  Cardinal.mk (ConnectedComponents S)

/-- The full canonical conjecture, over all positive dimensions and all real boxes. -/
def ComponentBoundConjecture : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (L U : RealMatrix n),
    EntrywiseLE L U → componentCard (realEigenvalueSet L U) ≤ (n : Cardinal)

/-- Colbrook's two independently varying entries in dimension three. -/
def family (a b : ℝ) : RealMatrix 3 :=
  !![25, a, b; 1, -1, 0; 1, 0, 1]

def lower : RealMatrix 3 := family (-166) 9

def upper : RealMatrix 3 := family (-16) 159

def includedValue : Fin 4 → ℝ := ![-3, 0, 3, 25]

def includedA : Fin 4 → ℝ := ![-21, -16, -146, -91]

def includedB : Fin 4 → ℝ := ![154, 9, 29, 84]

/-- Integer nonzero eigenvectors, including the eigenvalue-zero witness. -/
def includedVector : Fin 4 → Fin 3 → ℝ :=
  ![![-4, 2, 1], ![-1, -1, 1], ![4, 1, 2], ![312, 12, 13]]

def separator : Fin 3 → ℝ := ![-1, 1, 12]

def determinantLower : Fin 3 → ℝ := ![-332, -318, -3750]

def determinantUpper : Fin 3 → ℝ := ![-32, -18, -150]

end NLA.IV06
