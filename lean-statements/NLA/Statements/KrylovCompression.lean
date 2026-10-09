import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Shared concrete Gaussian, Krylov, Gram–Schmidt and condition-number
definitions for IE-10. A single recursive definition is imported by both the
live and frozen boundaries so their propositions are definitionally identical.
No target theorem or probability bound is asserted. -/
set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace NLA.Statements.KrylovCompression

abbrev Vector (n : ℕ) := Fin n → ℂ
abbrev GaussianSample (n : ℕ) := (Fin n × Fin 2) → ℝ

/-- Two independent real standard Gaussian coordinates per complex coordinate.
The common complex variance scale cancels when the vector is normalized. -/
noncomputable def GaussianLaw (n : ℕ) : Measure (GaussianSample n) :=
  Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 1)

def ComplexGaussian {n : ℕ} (z : GaussianSample n) : Vector n :=
  fun i => (z (i, 0) : ℂ) + Complex.I * (z (i, 1) : ℂ)

/-- The actual complex Euclidean norm, given by its full coordinate formula. -/
noncomputable def VectorNorm {n : ℕ} (v : Vector n) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

def Inner {n : ℕ} (u v : Vector n) : ℂ :=
  ∑ i, star (u i) * v i

/-- Unit-sphere start, with the zero Gaussian draw assigned the first basis vector.
On the n>=3 target domain that fallback is a genuine unit vector. -/
noncomputable def Start {n : ℕ} (z : GaussianSample n) : Vector n :=
  let g := ComplexGaussian z
  if 0 < VectorNorm g then
    fun i => g i / (VectorNorm g : ℂ)
  else
    fun i => if i.val = 0 then 1 else 0

/-- C e_j = e_(j+1 mod n), in zero-based indices. -/
def CyclicShift (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i.val = (j.val + 1) % n then 1 else 0

def Krylov {n : ℕ} (b : Vector n) (j : ℕ) : Vector n :=
  (CyclicShift n ^ j).mulVec b

/-- Subtract projections against exactly the preceding Gram–Schmidt columns. -/
def Residual {n : ℕ} (w : Vector n) (previous : List (Vector n)) : Vector n :=
  fun i => w i - (previous.map (fun q => q i * Inner q w)).sum

/-- The failed residual is assigned zero; success separately excludes every such case. -/
noncomputable def Normalize {n : ℕ} (u : Vector n) : Vector n :=
  if 0 < VectorNorm u then fun i => u i / (VectorNorm u : ℂ) else 0

/-- Finite, ordered Gram–Schmidt on b,Cb,...; no choice of a favorable basis occurs. -/
noncomputable def GramSchmidt {n : ℕ} (b : Vector n) : ℕ → List (Vector n)
  | 0 => []
  | j + 1 =>
      let previous := GramSchmidt b j
      previous ++ [Normalize (Residual (Krylov b j) previous)]

noncomputable def Column {n : ℕ} (b : Vector n) (j : ℕ) : Vector n :=
  Normalize (Residual (Krylov b j) (GramSchmidt b j))

def FullRank {n : ℕ} (b : Vector n) (k : ℕ) : Prop :=
  ∀ j : Fin k, 0 < VectorNorm (Residual (Krylov b j.val) (GramSchmidt b j.val))

noncomputable def Basis {n : ℕ} (b : Vector n) (k : ℕ) :
    Matrix (Fin n) (Fin k) ℂ :=
  fun i j => Column b j.val i

noncomputable def Compression {n : ℕ} (b : Vector n) (k : ℕ) :
    Matrix (Fin k) (Fin k) ℂ :=
  (Basis b k).conjTranspose * CyclicShift n * Basis b k

/-- The operator norm of the actual complex Euclidean continuous linear map. -/
noncomputable def SpectralNorm {k : ℕ} (V : Matrix (Fin k) (Fin k) ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin V)‖

/-- The infimum ranges over every genuine complex diagonalization. In ENNReal,
the empty infimum is infinity, exactly the nondiagonalizable convention.
There is no hypothesis that the infimum is attained. -/
noncomputable def EigenvectorCondition {k : ℕ} (H : Matrix (Fin k) (Fin k) ℂ) : ℝ≥0∞ :=
  sInf {y : ℝ≥0∞ |
    ∃ V : Matrix (Fin k) (Fin k) ℂ, ∃ d : Fin k → ℂ,
      V.det ≠ 0 ∧ H = V * Matrix.diagonal d * V⁻¹ ∧
      y = ENNReal.ofReal (SpectralNorm V * SpectralNorm V⁻¹)}

/-- Rank failures are excluded from every finite-threshold success event.
Their null probability in this specific cyclic-sphere model is a correspondence
fact, not an assumption passed into the target. -/
noncomputable def CompressionCondition {n : ℕ} (k : ℕ) (z : GaussianSample n) : ℝ≥0∞ := by
  classical
  exact if FullRank (Start z) k then
    EigenvectorCondition (Compression (Start z) k) else ⊤

end NLA.Statements.KrylovCompression
