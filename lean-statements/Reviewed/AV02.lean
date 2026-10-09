/- Frozen statement boundary. Changes reopen independent review. -/
import NLA.Computation.OracleMachine
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! AV-02: NP-hardness of the exact spectral condition threshold under
polynomial-time Turing reductions with only promised queries.
See docs/lean/statements/AV-02/NUMERICAL_TARGETS.md.
No reduction, NP-completeness theorem or target proof is asserted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Computation NLA.Computation.BinaryEncoding

namespace NLA.ReviewedStatements.AV02

/-- The entire closed diagonal cube, including both endpoint signs. -/
def InDiagonalCube {n : ℕ} (d : Fin n → ℝ) : Prop :=
  ∀ i, (-1 : ℝ) ≤ d i ∧ d i ≤ 1

def Perturbed (a : ThresholdInput) (d : Fin a.n → ℝ) :
    Matrix (Fin a.n) (Fin a.n) ℝ :=
  (Matrix.of fun i j => (a.matrix i j : ℝ)) - Matrix.diagonal d

/-- Every real diagonal perturbation must be nonsingular; no off-diagonal
entry varies and no spectral or triangular special case is imposed. -/
def Regular (a : ThresholdInput) : Prop :=
  ∀ d : Fin a.n → ℝ, InDiagonalCube d → (Perturbed a d).det ≠ 0

def InputPromise (a : ThresholdInput) : Prop :=
  1 ≤ a.n ∧ 0 < a.threshold ∧ Regular a

/-- The actual operator norm between real Euclidean spaces. -/
noncomputable def SpectralNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖

/-- On the regular input domain, compactness of the full cube and continuity
of inversion make this genuine finite supremum an attained maximum.
The determinant promise guards every inverse in this use of the definition. -/
noncomputable def ConditionNumber (a : ThresholdInput) : ℝ :=
  sSup {y : ℝ | ∃ d : Fin a.n → ℝ, InDiagonalCube d ∧
    y = SpectralNorm ((Perturbed a d)⁻¹)}

/-- Legal words are exactly the fixed full binary encoding of a promised
positive-dimensional rational matrix and positive rational threshold. -/
def LegalWords : Set NLA.Computation.Word :=
  {word | ∃ a : ThresholdInput, word = encodeThreshold a ∧ InputPromise a}

/-- Equality belongs to yes. Including the promise here makes this a literal
subset of LegalWords; oracle answers outside LegalWords remain unrestricted. -/
def YesWords : Set NLA.Computation.Word :=
  {word | ∃ a : ThresholdInput, word = encodeThreshold a ∧ InputPromise a ∧
    (a.threshold : ℝ) ≤ ConditionNumber a}

/-- Every concrete NP language reduces through the reviewed finite three-tape
oracle machine. One machine and polynomial bound precede all compatible oracles,
and every actual query in each required run must belong to LegalWords. -/
def Target : Prop :=
  Complexity.OracleNPHard LegalWords YesWords

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.AV02
