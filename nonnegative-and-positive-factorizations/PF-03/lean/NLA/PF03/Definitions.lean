/-
PF-03: transparent definitions for exact-source statement review.
Original mathematics and seed: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation, 13 September 2026.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with substantial Codex assistance.

UNELABORATED statement draft. No PF03 theorem is proved by this file.
RawData contains only literal rational arrays translated from pinned JSON.
The original target quantifies over every positive finite rational factor width.
Boundary means the frontier in the subtype of real symmetric matrices.
-/
import NLA.PF03.RawData
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

abbrev QMat (m n : ℕ) := Matrix (Fin m) (Fin n) ℚ
abbrev RMat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- The actual symmetric-matrix subspace, with its inherited subtype topology. -/
abbrev SymMatrix (F : Type) (n : ℕ) :=
  {A : Matrix (Fin n) (Fin n) F // A.IsSymm}

def castMatrix {m n : ℕ} (A : QMat m n) : RMat m n :=
  A.map (fun q : ℚ => (q : ℝ))

def castVector {n : ℕ} (x : Fin n → ℚ) : Fin n → ℝ :=
  fun i => (x i : ℝ)

/-- Only the already proved generic map-symmetry fact constructs the subtype. -/
def realCast {n : ℕ} (A : SymMatrix ℚ n) : SymMatrix ℝ n :=
  ⟨castMatrix A.val, A.property.map (fun q : ℚ => (q : ℝ))⟩

def CompletelyPositive {n : ℕ} (A : SymMatrix ℝ n) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ ∃ B : RMat n m,
    (∀ i j, 0 ≤ B i j) ∧ A.val = B * Bᵀ

def CPSet (n : ℕ) : Set (SymMatrix ℝ n) :=
  {A | CompletelyPositive A}

def RationalFactor {n : ℕ} (A : SymMatrix ℚ n) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ ∃ B : QMat n m,
    (∀ i j, 0 ≤ B i j) ∧ A.val = B * Bᵀ

/-- Unchanged canonical universal assertion; neither dimension nor width is bounded. -/
def RationalBoundaryFactorability : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ A : SymMatrix ℚ n,
    realCast A ∈ frontier (CPSet n) → RationalFactor A

def alpha : ℝ := Real.rpow 2 (1 / 3 : ℝ)
def ell : ℚ := 12599210498948731647672106072782283505702 / 10 ^ 40
def upp : ℚ := 12599210498948731647672106072782283505703 / 10 ^ 40

def alphaVector : Fin 3 → ℝ := ![1, alpha, alpha ^ 2]
def cubicZero : Cubic := ![0, 0, 0]
def cubicOne : Cubic := ![1, 0, 0]
def cubicAdd (x y : Cubic) : Cubic := fun i => x i + y i
def cubicMul (x y : Cubic) : Cubic :=
  ![x 0 * y 0 + 2 * x 1 * y 2 + 2 * x 2 * y 1,
    x 0 * y 1 + x 1 * y 0 + 2 * x 2 * y 2,
    x 0 * y 2 + x 1 * y 1 + x 2 * y 0]

def cubicEval (x : Cubic) : ℝ :=
  (x 0 : ℝ) + (x 1 : ℝ) * alpha + (x 2 : ℝ) * alpha ^ 2

def seedC (i : Fin 7) : QMat 7 3 :=
  fun r k => RawData.coefficientMatrices k r i

def seedColumn (i : Fin 7) : Fin 7 → ℝ :=
  (castMatrix (seedC i)).mulVec alphaVector

def orthogonalSeed : RMat 7 7 := fun r i => seedColumn i r
def orthogonalCache : RMat 7 7 := RawData.orthogonalMatrix.map cubicEval
def quadraticSeed : RMat 7 7 := RawData.quadraticMatrix.map cubicEval
def localCache (i : Fin 7) : RMat 3 3 := (RawData.restrictedGram i).map cubicEval
def localForm (i : Fin 7) : RMat 3 3 :=
  (castMatrix (seedC i))ᵀ * quadraticSeed * castMatrix (seedC i)

/-- The seven fixed 2-by-2 minors selected in the original exact preflight. -/
def seedMinor (i : Fin 7) : ℚ :=
  seedC i 0 0 * seedC i 1 1 - seedC i 0 1 * seedC i 1 0

def HasNonzeroMinor (C : QMat 7 3) : Prop :=
  ∃ r s : Fin 7, ∃ a b : Fin 3, C r a * C s b - C r b * C s a ≠ 0

def centerA : ℚ := 125992104989487316477 / 10 ^ 20
def centerB : ℚ := 158740105196819947475 / 10 ^ 20
def triangleDelta : ℚ := 1 / 10000

def triangle : QMat 3 3 :=
  ![![1, 1, 1],
    ![centerA + triangleDelta, centerA, centerA - triangleDelta],
    ![centerB, centerB + triangleDelta, centerB - triangleDelta]]

def dx : ℝ := (alpha - (centerA : ℝ)) / (triangleDelta : ℝ)
def dy : ℝ := (alpha ^ 2 - (centerB : ℝ)) / (triangleDelta : ℝ)
def barycentric : Fin 3 → ℝ :=
  ![(1 + 2 * dx - dy) / 3, (1 - dx + 2 * dy) / 3, (1 - dx - dy) / 3]

def generator (i : Fin 7) (j : Fin 3) : Fin 7 → ℚ :=
  fun r => (seedC i * triangle) r j

/-- The j-th column has pair index (j / 3,j % 3), the original lexicographic order. -/
def generatorMatrix : QMat 7 21 :=
  fun r j =>
    generator ((finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21).symm j).1
      ((finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21).symm j).2 r

def positiveSlice : Fin 7 → ℚ :=
  ![-71246841 / 10 ^ 8, -101280383 / 10 ^ 8, -150296097 / 10 ^ 8,
    -110993458 / 10 ^ 8, -39802169 / 10 ^ 8, -119030527 / 10 ^ 8,
    -63286873 / 10 ^ 8]

def bilinear {d : ℕ} (Q : RMat d d) (x y : Fin d → ℝ) : ℝ :=
  ∑ r : Fin d, ∑ s : Fin d, x r * Q r s * y s
def quad {d : ℕ} (Q : RMat d d) (x : Fin d → ℝ) : ℝ := bilinear Q x x

/-- Literal conical combinations with arbitrary nonnegative REAL coefficients. -/
def Cone {d s : ℕ} (V : QMat d s) : Set (Fin d → ℝ) :=
  {x | ∃ lam : Fin s → ℝ, (∀ j, 0 ≤ lam j) ∧
    x = (castMatrix V).mulVec lam}

def K : Set (Fin 7 → ℝ) := Cone generatorMatrix
def localCone (i : Fin 7) : Set (Fin 7 → ℝ) := Cone (seedC i * triangle)
def HSet {N d : ℕ} (R : QMat N d) : Set (Fin d → ℝ) :=
  {x | ∀ i, 0 ≤ ((castMatrix R).mulVec x) i}

/-- Literal no-line condition, not Mathlib's weaker ConvexCone.Pointed property. -/
def NoLine {d : ℕ} (S : Set (Fin d → ℝ)) : Prop :=
  ∀ x, x ∈ S → -x ∈ S → x = 0

def rowHolds {d : ℕ} (r : Fin d → ℚ) (x : Fin d → ℝ) : Prop :=
  0 ≤ ∑ j : Fin d, (r j : ℝ) * x j

/-- Explicit Fourier–Motzkin output: zero rows and all positive-negative pairs.
Empty lists, zero coefficients and one-sided systems are included literally. -/
def eliminateOne {N d : ℕ} (A : QMat N d) (a : Fin N → ℚ) :
    List (Fin d → ℚ) :=
  ((List.finRange N).filterMap (fun i => if a i = 0 then some (A i) else none)) ++
    (List.finRange N).flatMap (fun p =>
      (List.finRange N).filterMap (fun q =>
        if 0 < a p ∧ a q < 0 then
          some (fun j => a p * A q j - a q * A p j)
        else none))

def MixedHolds {N d m : ℕ} (A : QMat N d) (B : QMat N m)
    (x : Fin d → ℝ) (y : Fin m → ℝ) : Prop :=
  ∀ i, 0 ≤ ((castMatrix A).mulVec x) i + ((castMatrix B).mulVec y) i

/-- Append exactly five zero rows; no facet enumeration or chosen H-representation. -/
def padRows {N : ℕ} (R : QMat N 7) : QMat (N + 5) 7 :=
  Fin.append R (0 : QMat 5 7)

def paddedIndex (N : ℕ) : Fin (N + 5) := Fin.natAdd N (0 : Fin 5)

/-- The symmetry proof is the generic rectangular Gram-matrix identity. -/
def paddedGram {N : ℕ} (R : QMat N 7) : SymMatrix ℚ (N + 5) :=
  ⟨padRows R * (padRows R)ᵀ, by
    change (padRows R * (padRows R)ᵀ)ᵀ = padRows R * (padRows R)ᵀ
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]⟩

def paddedRealFactor {N : ℕ} (R : QMat N 7) : RMat (N + 5) 7 :=
  castMatrix (padRows R) * orthogonalSeed

end NLA.PF03
