import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-! The real Hadamard and complete-pivoting predicates for IE-03. -/

namespace NLA.IE03

/-- Entries are indexed from zero. A matrix of order `n` uses only indices below `n`. -/
abbrev Entries (K : Type*) := ℕ → ℕ → K

/-- Increasing enumeration of the indices remaining after deleting `r`. -/
def skip (r i : ℕ) : ℕ :=
  if i < r then i else i + 1

/-- The active Schur complement after pivoting at row `r`, column `c`.
The two selected indices are deleted and the other indices keep their order. -/
def schur {K : Type*} [Field K] (A : Entries K) (r c : ℕ) : Entries K :=
  fun i j =>
    A (skip r i) (skip c j) - A (skip r i) c * A r (skip c j) / A r c

/-- A legal complete pivot in the entire active square of order `n`. -/
def IsPivot {K : Type*} [Field K] [LinearOrder K]
    (n : ℕ) (A : Entries K) (r c : ℕ) : Prop :=
  r < n ∧ c < n ∧ A r c ≠ 0 ∧
    ∀ i j, i < n → j < n → |A i j| ≤ |A r c|

/-- A finite prefix of a complete-pivoting path, with its last active matrix
and the maximum magnitude of the pivots taken so far. The empty maximum is zero. -/
inductive PivotPrefix {K : Type*} [Field K] [LinearOrder K] :
    ℕ → Entries K → ℕ → Entries K → K → Prop where
  | empty (n : ℕ) (A : Entries K) : PivotPrefix n A n A 0
  | step {n m : ℕ} {A B : Entries K} {g : K} (r c : ℕ)
      (h : IsPivot (n + 1) A r c) (tail : PivotPrefix n (schur A r c) m B g) :
      PivotPrefix (n + 1) A m B (max |A r c| g)

/-- A complete path eliminates the entire active matrix. Its maximum pivot
magnitude is the maximum magnitude of an entry over all its active matrices. -/
def CompletePath (n : ℕ) (A : Entries ℝ) (g : ℝ) : Prop :=
  ∃ B, PivotPrefix n A 0 B g

/-- Real sign entries and the row Gram identity `A Aᵀ = n I`. -/
def IsHadamard (n : ℕ) (A : Entries ℝ) : Prop :=
  (∀ i j, i < n → j < n → A i j = 1 ∨ A i j = -1) ∧
  (∀ i j, i < n → j < n →
    (∑ k ∈ Finset.range n, A i k * A j k) = if i = j then (n : ℝ) else 0)

end NLA.IE03
