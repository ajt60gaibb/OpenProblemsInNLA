/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! RA-04: the exact clustered-gap block Krylov probability target.
The full pre-reviewed specification is docs/lean/statements/RA-04/NUMERICAL_TARGETS.md.
No approximation theorem or probability estimate is proved by this definition. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace NLA.ReviewedStatements.RA04

/-- The actual descending singular values, with the library's zero padding. -/
noncomputable def SingularValue {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (i : ℕ) : ℝ := (Matrix.toEuclideanLin A).singularValues i

def BlockCount (k b : ℕ) : ℕ := (k + b - 1) / b

def PaddedRank (k b : ℕ) : ℕ := b * BlockCount k b

/-- Exactly the b-step relative squared-singular-value gap; empty minimum is one. -/
noncomputable def BlockGap {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (m b : ℕ) : ℝ :=
  if m - b = 0 then 1 else
    sInf {x : ℝ | ∃ i : Fin (m - b),
      x = (SingularValue A i.val ^ 2 - SingularValue A (i.val + b) ^ 2) /
        SingularValue A i.val ^ 2}

/-- Natural ceilings of the precise real iteration formula, with no added logarithm. -/
noncomputable def StepCount (C ε δ : ℝ) (n k b : ℕ) (gap : ℝ) : ℕ :=
  Nat.ceil (C * ((BlockCount k b : ℝ) / Real.sqrt ε * Real.log (2 / gap) +
    (1 / Real.sqrt ε) * Real.log ((n : ℝ) / (δ * ε))))

abbrev Sample (n b : ℕ) := (Fin n × Fin b) → ℝ

noncomputable def GaussianLaw (n b : ℕ) : Measure (Sample n b) :=
  Measure.pi (fun _ : Fin n × Fin b => gaussianReal 0 1)

def DrawMatrix {n b : ℕ} (z : Sample n b) : Matrix (Fin n) (Fin b) ℝ :=
  fun i j => z (i, j)

/-- The actual real span of every block column at powers zero through q-1. -/
def KrylovSpace {n d b : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (G : Matrix (Fin n) (Fin b) ℝ) (q : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range (fun ja : Fin q × Fin b =>
    ((A * A.transpose) ^ ja.1.val).mulVec (fun i => G i ja.2)))

def OrthonormalColumns {n r : ℕ} (Z : Matrix (Fin n) (Fin r) ℝ) : Prop :=
  ∀ i j, (∑ a, Z a i * Z a j) = if i = j then 1 else 0

/-- Both orthonormality and equality with the complete Krylov space are mandatory. -/
def IsKrylovBasis {n d b r : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (G : Matrix (Fin n) (Fin b) ℝ) (q : ℕ)
    (Z : Matrix (Fin n) (Fin r) ℝ) : Prop :=
  OrthonormalColumns Z ∧
    Submodule.span ℝ (Set.range (fun j => fun i => Z i j)) = KrylovSpace A G q

/-- Full ordered orthogonal diagonalization of B transpose B. This retains all
right singular-vector bases, including every tied and zero singular subspace. -/
def RightSpectrum {r d : ℕ} (B : Matrix (Fin r) (Fin d) ℝ)
    (eigenvalues : Fin d → ℝ) (V : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ i, 0 ≤ eigenvalues i) ∧ Antitone eigenvalues ∧ OrthonormalColumns V ∧
    ∀ i j, (∑ a, B a i * B a j) = ∑ a, eigenvalues a * V i a * V j a

/-- The actual truncated SVD B times its chosen leading right-space projector. -/
def Truncate {r d : ℕ} (B : Matrix (Fin r) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) : Matrix (Fin r) (Fin d) ℝ :=
  fun i j => ∑ a : Fin d,
    if a.val < k then (∑ h, B i h * V h a) * V j a else 0

noncomputable def SpectralNorm {n d : ℕ} (B : Matrix (Fin n) (Fin d) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)‖

noncomputable def FrobeniusNorm {n d : ℕ} (B : Matrix (Fin n) (Fin d) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, B i j ^ 2)

/-- The exact optimal rank-k Frobenius error, including zero tails. -/
noncomputable def FrobeniusTail {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (k : ℕ) : ℝ :=
  Real.sqrt (∑ i : Fin (min n d), if k ≤ i.val then SingularValue A i.val ^ 2 else 0)

/-- All three guarantees for the same output. The vector index runs over all
first k columns of every ordered right decomposition of that output. -/
def GoodOutput {n d : ℕ} (A Ahat : Matrix (Fin n) (Fin d) ℝ)
    (k : ℕ) (ε : ℝ) : Prop :=
  SpectralNorm (A - Ahat) ≤ (1 + ε) * SingularValue A k ∧
  FrobeniusNorm (A - Ahat) ≤ (1 + ε) * FrobeniusTail A k ∧
  ∀ eigenvalues : Fin d → ℝ, ∀ W : Matrix (Fin d) (Fin d) ℝ,
    RightSpectrum Ahat eigenvalues W →
      ∀ i : Fin d, i.val < k →
        |(∑ a : Fin n, (∑ j : Fin d, A a j * W j i) ^ 2) -
            SingularValue A i.val ^ 2| ≤ ε * SingularValue A k ^ 2

/-- One draw succeeds for every allowed basis and SVD truncation choice.
No favorable choice, resampling, rank-failure deletion or changed subspace occurs. -/
def Success {n d b : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (G : Matrix (Fin n) (Fin b) ℝ) (k q : ℕ) (ε : ℝ) : Prop :=
  ∀ r : ℕ, ∀ Z : Matrix (Fin n) (Fin r) ℝ,
    IsKrylovBasis A G q Z →
      ∀ eigenvalues : Fin d → ℝ, ∀ V : Matrix (Fin d) (Fin d) ℝ,
        RightSpectrum (Z.transpose * A) eigenvalues V →
          GoodOutput A (Z * Truncate (Z.transpose * A) V k) k ε

/-- The universal constant precedes every matrix, dimension, block, rank and
accuracy/failure parameter. There is precisely one event for the three bounds. -/
def Target : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n d b k : ℕ, ∀ A : Matrix (Fin n) (Fin d) ℝ,
      1 ≤ b → b ≤ k → PaddedRank k b ≤ A.rank →
      0 < BlockGap A (PaddedRank k b) b →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 →
        ENNReal.ofReal (1 - δ) ≤
          GaussianLaw n b {z |
            Success A (DrawMatrix z) k
              (StepCount C ε δ n k b (BlockGap A (PaddedRank k b) b)) ε}

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.RA04
