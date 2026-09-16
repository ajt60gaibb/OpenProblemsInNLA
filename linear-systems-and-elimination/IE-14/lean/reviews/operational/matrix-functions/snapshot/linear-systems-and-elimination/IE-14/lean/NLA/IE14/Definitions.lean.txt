/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
Statement preparation only: no proof implementation.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators NNReal
namespace NLA.IE14

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev PivotPath (n : ℕ) := Fin n → Fin n

/-- Literal row swaps in the fixed original column ordering. -/
def rowSwap {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  fun i j => S (Equiv.swap k p i) j

/-- Exact Schur update, padded by zero off the new active block. -/
def schurStep {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  let B := rowSwap S k p
  fun i j => if k < i ∧ k < j then B i j - (B i k / B k k) * B k j else 0

/-- Stage zero is the actual input; no preliminary permutation is performed. -/
def trajectory {n : ℕ} (A : Mat n) (path : PivotPath n) : ℕ → Mat n
  | 0 => A
  | k+1 => if h : k<n then schurStep (trajectory A path k) ⟨k,h⟩ (path ⟨k,h⟩) else 0

def AdmissiblePivot {n : ℕ} (S : Mat n) (k p : Fin n) : Prop :=
  k ≤ p ∧ S p k ≠ 0 ∧ ∀ i, k ≤ i → ‖S i k‖ ≤ ‖S p k‖

/-- Every maximal-modulus tie is permitted. -/
def AdmissiblePath {n : ℕ} (A : Mat n) (path : PivotPath n) : Prop :=
  ∀ k, AdmissiblePivot (trajectory A path k.val) k (path k)

def entryMaxNN {n : ℕ} (A : Mat n) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊)

def entryMax {n : ℕ} (A : Mat n) : ℝ := entryMaxNN A

def activeMaxNN {n : ℕ} (S : Mat n) (k : ℕ) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n =>
    if k ≤ ij.1.val ∧ k ≤ ij.2.val then ‖S ij.1 ij.2‖₊ else 0)

def activeMax {n : ℕ} (S : Mat n) (k : ℕ) : ℝ := activeMaxNN S k

/-- All n active stages, including the input and final scalar, enter the numerator. -/
def growth {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ) /
    entryMax A

def CyclicPosition {n : ℕ} (i j : Fin n) : Prop :=
  (i.val ≤ j.val+1 ∧ j.val ≤ i.val+1) ∨
    (i.val=0 ∧ j.val+1=n) ∨ (j.val=0 ∧ i.val+1=n)

/-- Nonsingular complex cyclic tridiagonal matrices with both actual corner entries nonzero. -/
def CyclicInput {n : ℕ} (A : Mat n) : Prop :=
  A.det ≠ 0 ∧ (∀ i j, ¬CyclicPosition i j → A i j=0) ∧
    ∀ i j : Fin n, i.val=0 → j.val+1=n → A i j ≠ 0 ∧ A j i ≠ 0

def cyclicGrowthSet (n : ℕ) : Set ℝ :=
  {r | ∃ A : Mat n, ∃ path : PivotPath n, CyclicInput A ∧ AdmissiblePath A path ∧ r=growth A path}

def sharpConstant (n : ℕ) : ℝ := sSup (cyclicGrowthSet n)
def fibonacciBound (n : ℕ) : ℝ := (Nat.fib (n+1) : ℝ) + 1

def witnessLower (n : ℕ) : Mat n := fun i j =>
  if i=j then 1 else if j.val+1=i.val ∨ j.val+2=i.val then -1 else 0

def witnessUpper (n : ℕ) : Mat n := fun i j =>
  if j.val+1=n then (if i=j then (Nat.fib (n+1) : ℂ)+1 else (Nat.fib (i.val+2) : ℂ))
  else if i=j then (if i.val=1 then 1/2 else 1)
  else if i.val=0 ∧ j.val=1 then 1/2 else 0

/-- Inverse of the factor-row labeling (1,n,2,...,n-1), used only to define the input. -/
def factorIndex (n : ℕ) (hn : 4 ≤ n) (i : Fin n) : Fin n :=
  if h0 : i.val=0 then ⟨0, by omega⟩
  else if hlast : i.val+1=n then ⟨1, by omega⟩ else ⟨i.val+1, by omega⟩

def witnessMatrix (n : ℕ) (hn : 4 ≤ n) : Mat n :=
  fun i j => (witnessLower n * witnessUpper n) (factorIndex n hn i) j

/-- Actual successive swaps: keep the first row, then select the current last row at each stage. -/
def witnessPath (n : ℕ) (hn : 4 ≤ n) : PivotPath n :=
  fun k => if k.val=0 then k else ⟨n-1, by omega⟩

end NLA.IE14
