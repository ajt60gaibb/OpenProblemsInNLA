import NLA.Computation.FiniteMachine
import NLA.Computation.BinaryEncoding
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Exact compact tridiagonal interval inputs and exact range/hull outputs.
The semantics include every independent real interval choice. The encoding
uses the previously reviewed canonical rational syntax and counts all bits.
No algorithm, complexity bound or oracle is supplied by this helper module. -/
set_option autoImplicit false

open scoped BigOperators

namespace NLA.Computation.BandIntervals

open BinaryEncoding

/-- Syntax is separate from the ordered-endpoint input condition. -/
structure RationalInterval where
  lower : ℚ
  upper : ℚ

def RationalInterval.Ordered (a : RationalInterval) : Prop := a.lower ≤ a.upper

def RationalInterval.Contains (a : RationalInterval) (x : ℝ) : Prop :=
  (a.lower : ℝ) ≤ x ∧ x ≤ (a.upper : ℝ)

def encodeInterval (a : RationalInterval) : Word :=
  encodeRat a.lower ++ encodeRat a.upper

/-- Exactly n + (n-1) + (n-1) intervals, not a dense matrix encoding. -/
structure BandInput where
  n : ℕ
  diagonal : Fin n → RationalInterval
  upper : Fin (n - 1) → RationalInterval
  lower : Fin (n - 1) → RationalInterval

def BandInput.Ordered (a : BandInput) : Prop :=
  (∀ i, (a.diagonal i).Ordered) ∧
  (∀ i, (a.upper i).Ordered) ∧ (∀ i, (a.lower i).Ordered)

/-- Increasing coordinate order within each band, diagonal then upper then lower. -/
def encodeBand (a : BandInput) : Word :=
  encodeNat a.n ++
    (List.ofFn a.diagonal).flatMap encodeInterval ++
    (List.ofFn a.upper).flatMap encodeInterval ++
    (List.ofFn a.lower).flatMap encodeInterval

/-- First endpoint of an edge between successive matrix coordinates. -/
def edgeLeft {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, by have h := i.isLt; omega⟩

/-- Second endpoint; subtraction in the band length never wraps the edge. -/
def edgeRight {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by have h := i.isLt; omega⟩

/-- All real matrix entries vary independently. Only positions outside the
three bands are forced to zero. Equal interval endpoints do not tie entries. -/
def MatrixMember (a : BandInput) (T : Matrix (Fin a.n) (Fin a.n) ℝ) : Prop :=
  (∀ i, (a.diagonal i).Contains (T i i)) ∧
  (∀ i, (a.upper i).Contains (T (edgeLeft i) (edgeRight i))) ∧
  (∀ i, (a.lower i).Contains (T (edgeRight i) (edgeLeft i))) ∧
  (∀ i j, i ≠ j → i.val + 1 ≠ j.val → j.val + 1 ≠ i.val → T i j = 0)

/-- Actual minimum and maximum, with separate attaining matrices. -/
def CorrectRange (a : BandInput) (dlo dhi : ℚ) : Prop :=
  (∀ T : Matrix (Fin a.n) (Fin a.n) ℝ, MatrixMember a T →
    (dlo : ℝ) ≤ T.det ∧ T.det ≤ (dhi : ℝ)) ∧
  (∃ T : Matrix (Fin a.n) (Fin a.n) ℝ, MatrixMember a T ∧ T.det = (dlo : ℝ)) ∧
  (∃ T : Matrix (Fin a.n) (Fin a.n) ℝ, MatrixMember a T ∧ T.det = (dhi : ℝ))

def encodeRange (dlo dhi : ℚ) : Word := encodeRat dlo ++ encodeRat dhi

structure SystemInput where
  band : BandInput
  rhs : Fin band.n → RationalInterval

def SystemInput.Ordered (a : SystemInput) : Prop :=
  a.band.Ordered ∧ ∀ i, (a.rhs i).Ordered

/-- One dimension header: compact band data followed by all RHS intervals. -/
def encodeSystem (a : SystemInput) : Word :=
  encodeBand a.band ++ (List.ofFn a.rhs).flatMap encodeInterval

def RhsMember (a : SystemInput) (b : Fin a.band.n → ℝ) : Prop :=
  ∀ i, (a.rhs i).Contains (b i)

/-- The full united real solution set, including singular and inconsistent
systems; no inverse or regularity hypothesis is used. -/
def SolutionSet (a : SystemInput) : Set (Fin a.band.n → ℝ) :=
  {x | ∃ T : Matrix (Fin a.band.n) (Fin a.band.n) ℝ, ∃ b : Fin a.band.n → ℝ,
    MatrixMember a.band T ∧ RhsMember a b ∧ T.mulVec x = b}

inductive LowerEndpoint where
  | negativeInfinity
  | finite (q : ℚ)

inductive UpperEndpoint where
  | finite (q : ℚ)
  | positiveInfinity

/-- Emptiness is global, not an independent coordinate output. -/
inductive HullOutput (n : ℕ) where
  | empty
  | box (lower : Fin n → LowerEndpoint) (upper : Fin n → UpperEndpoint)

def encodeLower : LowerEndpoint → Word
  | .negativeInfinity => [false]
  | .finite q => true :: encodeRat q

def encodeUpper : UpperEndpoint → Word
  | .finite q => true :: encodeRat q
  | .positiveInfinity => [false]

/-- In a nonempty output the original dimension and every coordinate pair
are explicit. A false endpoint tag means the infinity appropriate to its side. -/
def encodeHull {n : ℕ} : HullOutput n → Word
  | .empty => [false]
  | .box lower upper =>
      [true] ++ encodeNat n ++
        (List.ofFn (fun i : Fin n => encodeLower (lower i) ++ encodeUpper (upper i))).flatten

/-- Lower infimum semantics. Finite endpoints require arbitrarily close
solutions, not attainment and not equality of the projection with an interval. -/
def LowerCorrect {n : ℕ} (S : Set (Fin n → ℝ)) (i : Fin n) : LowerEndpoint → Prop
  | .negativeInfinity => ∀ R : ℝ, ∃ x ∈ S, x i < R
  | .finite q =>
      (∀ x ∈ S, (q : ℝ) ≤ x i) ∧
      (∀ ε : ℝ, 0 < ε → ∃ x ∈ S, x i < (q : ℝ) + ε)

/-- Upper supremum semantics, including genuinely unbounded coordinates. -/
def UpperCorrect {n : ℕ} (S : Set (Fin n → ℝ)) (i : Fin n) : UpperEndpoint → Prop
  | .finite q =>
      (∀ x ∈ S, x i ≤ (q : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ x ∈ S, (q : ℝ) - ε < x i)
  | .positiveInfinity => ∀ R : ℝ, ∃ x ∈ S, R < x i

/-- Exact smallest coordinate box, retaining disconnected solution projections. -/
def CorrectHull (a : SystemInput) : HullOutput a.band.n → Prop
  | .empty => SolutionSet a = ∅
  | .box lower upper =>
      (SolutionSet a).Nonempty ∧
      ∀ i, LowerCorrect (SolutionSet a) i (lower i) ∧
        UpperCorrect (SolutionSet a) i (upper i)

end NLA.Computation.BandIntervals
