import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# IE-05: exact definitions for statement review

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.

The original extremizer conjecture is attributed to John Peca-Medlin; the
order-eight counterexample is Stepaniants's AI-assisted 2026 manuscript.
This module contains definitions, not a proof of that counterexample.
-/

noncomputable section
open scoped BigOperators NNReal

namespace NLA.IE05

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev IntMat (n : ℕ) := Matrix (Fin n) (Fin n) ℤ
abbrev PivotPath (n : ℕ) := Fin n → Fin n

/-- Actual real column orthogonality, with no spectral or pivot assumptions. -/
def Orthogonal {n : ℕ} (A : Mat n) : Prop := A.transpose * A = 1

def UpperTriangular {n : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin n) (Fin n) R) : Prop := ∀ i j, j < i → A i j = 0

def UnitLower {n : ℕ} {R : Type*} [Zero R] [One R]
    (A : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, i < j → A i j = 0

def prescribedLower (n : ℕ) : Mat n :=
  fun i j => if i = j then 1 else if j < i then -1 else 0

/-- These are L2 Euclidean columns, not the coordinatewise supremum norm. -/
def euclideanColumns {n : ℕ} (A : Mat n) : Fin n → EuclideanSpace ℝ (Fin n) :=
  fun j => WithLp.toLp 2 (fun i => A i j)

/-- Mathlib's normalized Gram--Schmidt, in the usual increasing `Fin n` order. -/
def normalizedQRQ {n : ℕ} (A : Mat n) : Mat n :=
  fun i j => InnerProductSpace.gramSchmidtNormed ℝ (euclideanColumns A) j i

def candidateQ (n : ℕ) : Mat n := normalizedQRQ (prescribedLower n)
def candidateR (n : ℕ) : Mat n := (candidateQ n).transpose * prescribedLower n

def PositiveQR {n : ℕ} (A Q R : Mat n) : Prop :=
  Orthogonal Q ∧ A = Q * R ∧ UpperTriangular R ∧ ∀ i, 0 < R i i

/-- Swap the current row positions; no column exchange occurs in partial pivoting. -/
def rowSwap {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  fun i j => S (Equiv.swap k p i) j

/-- The actual Schur update, padded by zero outside the new active trailing block.
Division is total in Lean; `AdmissiblePivot` separately requires a nonzero pivot. -/
def schurStep {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  let B := rowSwap S k p
  fun i j => if k < i ∧ k < j then
    B i j - (B i k / B k k) * B k j else 0

/-- Stage zero is the input; stages `0,...,n-1` are the active Schur complements. -/
def trajectory {n : ℕ} (A : Mat n) (path : PivotPath n) : ℕ → Mat n
  | 0 => A
  | k + 1 => if h : k < n then
      schurStep (trajectory A path k) ⟨k, h⟩ (path ⟨k, h⟩) else 0

def AdmissiblePivot {n : ℕ} (S : Mat n) (k p : Fin n) : Prop :=
  k ≤ p ∧ S p k ≠ 0 ∧ ∀ i, k ≤ i → |S i k| ≤ |S p k|

def FirstAvailablePivot {n : ℕ} (S : Mat n) (k p : Fin n) : Prop :=
  AdmissiblePivot S k p ∧
    ∀ i, k ≤ i → |S i k| = |S p k| → p ≤ i

def AdmissiblePath {n : ℕ} (A : Mat n) (path : PivotPath n) : Prop :=
  ∀ k, AdmissiblePivot (trajectory A path k.val) k (path k)

def FirstAvailablePath {n : ℕ} (A : Mat n) (path : PivotPath n) : Prop :=
  ∀ k, FirstAvailablePivot (trajectory A path k.val) k (path k)

/-- A deterministic ascending-row scan. Equal magnitudes never replace the current row. -/
def firstPivotIndex {n : ℕ} (S : Mat n) (k : Fin n) : Fin n :=
  (List.finRange n).foldl
    (fun p i => if k ≤ i ∧ |S p k| < |S i k| then i else p) k

def firstTrajectory {n : ℕ} (A : Mat n) : ℕ → Mat n
  | 0 => A
  | k + 1 => if h : k < n then
      schurStep (firstTrajectory A k) ⟨k, h⟩
        (firstPivotIndex (firstTrajectory A k) ⟨k, h⟩) else 0

def firstPath {n : ℕ} (A : Mat n) : PivotPath n :=
  fun k => firstPivotIndex (firstTrajectory A k.val) k

def noSwapPath (n : ℕ) : PivotPath n := fun k => k

/-- Finite maximum of absolute real entries, implemented as a supremum in `ℝ≥0`. -/
def entryMaxNN {n : ℕ} (A : Mat n) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊)

def entryMax {n : ℕ} (A : Mat n) : ℝ := entryMaxNN A

def activeMaxNN {n : ℕ} (S : Mat n) (k : ℕ) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n =>
    if k ≤ ij.1.val ∧ k ≤ ij.2.val then ‖S ij.1 ij.2‖₊ else 0)

def activeMax {n : ℕ} (S : Mat n) (k : ℕ) : ℝ := activeMaxNN S k

/-- All and only the `n` active stages enter the growth numerator. -/
def growth {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n =>
    activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ) / entryMax A

def firstGrowth {n : ℕ} (A : Mat n) : ℝ := growth A (firstPath A)

/-- Every orthogonal input and every admissible partial-pivoting path is included. -/
def orthogonalGrowthSet (n : ℕ) : Set ℝ :=
  {r | ∃ A : Mat n, Orthogonal A ∧
    ∃ path : PivotPath n, AdmissiblePath A path ∧ r = growth A path}

/-- The actual conditionally complete real supremum. No boundedness is assumed here. -/
def orthogonalGrowthSup (n : ℕ) : ℝ := sSup (orthogonalGrowthSet n)

def OrthogonalExtremizerConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → orthogonalGrowthSup n = firstGrowth (candidateQ n)

def scaledColumns {n : ℕ} (A : Mat n) (d : Fin n → ℝ) : Mat n :=
  fun i j => A i j / Real.sqrt (d j)

/-- The product of the two trailing factors, still padded by zero. -/
def tailProduct {n : ℕ} {R : Type*} [Semiring R]
    (L T : Matrix (Fin n) (Fin n) R) (k : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if k ≤ i.val ∧ k ≤ j.val then
    ∑ r : Fin n, if k ≤ r.val then L i r * T r j else 0 else 0

def integerLower (b : Bool) : IntMat 8 :=
  fun i j => if i = j then 1 else if j < i then
    if b = true ∧ i = 7 ∧ j = 1 then 0 else -1 else 0

/-- `false` is the prescribed candidate; `true` changes one-based entry (8,2). -/
def integerH : Bool → IntMat 8
  | false => ![
      ![1,-5,-8,-12,-16,-16,0,64], ![-1,13,-4,-6,-8,-8,0,32],
      ![-1,-3,51,-3,-4,-4,0,16], ![-1,-3,-11,169,-2,-2,0,8],
      ![-1,-3,-11,-43,511,-1,0,4], ![-1,-3,-11,-43,-171,1365,0,2],
      ![-1,-3,-11,-43,-171,-683,1,1], ![-1,-3,-11,-43,-171,-683,-1,1]]
  | true => ![
      ![1,-1,-3,-21,-41,-101,-325,63], ![-1,3,1,17,71,291,1179,31],
      ![-1,-1,13,-19,-56,-196,-752,16], ![-1,-1,-3,189,-28,-98,-376,8],
      ![-1,-1,-3,-51,581,-49,-188,4], ![-1,-1,-3,-51,-213,1507,-94,2],
      ![-1,-1,-3,-51,-213,-873,2589,1], ![-1,1,-5,-55,-183,-683,-2683,1]]

def integerD : Bool → Fin 8 → ℤ
  | false => ![8,248,3286,36146,349184,2796544,2,5462]
  | true => ![8,16,240,47640,472430,3644970,16148136,5272]

def integerT : Bool → IntMat 8
  | false => ![
      ![1,-5,-8,-12,-16,-16,0,64], ![0,8,-12,-18,-24,-24,0,96],
      ![0,0,31,-33,-44,-44,0,176], ![0,0,0,106,-86,-86,0,344],
      ![0,0,0,0,341,-171,0,684], ![0,0,0,0,0,1024,0,1366],
      ![0,0,0,0,0,0,1,2731], ![0,0,0,0,0,0,0,5462]]
  | true => ![
      ![1,-1,-3,-21,-41,-101,-325,63], ![0,2,-2,-4,30,190,854,94],
      ![0,0,8,-44,-67,-107,-223,173], ![0,0,0,120,-106,-116,-70,338],
      ![0,0,0,0,397,-183,48,672], ![0,0,0,0,0,1190,190,1342],
      ![0,0,0,0,0,0,3063,2683], ![0,0,0,0,0,0,0,5272]]

def castIntegerMatrix {n : ℕ} (A : IntMat n) : Mat n :=
  fun i j => (A i j : ℝ)

def normalizedInteger (b : Bool) : Mat 8 :=
  scaledColumns (castIntegerMatrix (integerH b)) (fun j => (integerD b j : ℝ))

def witnessQ : Mat 8 := normalizedInteger true

end NLA.IE05
