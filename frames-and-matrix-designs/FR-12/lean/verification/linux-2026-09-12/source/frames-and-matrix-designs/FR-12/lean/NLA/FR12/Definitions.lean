/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Definitions for the full FR-12 labeled real Hadamard counting conjecture.
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. Substantial AI-agent assistance.
-/
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace NLA.FR12

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Exactly the canonical labeled real sign matrices and one-sided Gram identity.
There is no quotient by row/column permutations or signs. -/
def IsRealHadamard {n : ℕ} (A : Mat n) : Prop :=
  (∀ i j, A i j = 1 ∨ A i j = -1) ∧
    A * A.transpose = (n : ℝ) • (1 : Mat n)

/-- Individual matrices, with their original row and column labels. -/
def HadamardMatrices (n : ℕ) := {A : Mat n // IsRealHadamard A}

/-- The exact finite count. Finiteness of the displayed matrix subtype is a
required theorem, so `Nat.card` is not used to hide an infinite set. -/
def hadamardCount (n : ℕ) : ℕ := Nat.card (HadamardMatrices n)

/-- The complete original conjecture, including every positive multiple of four
and an arbitrary positive real constant. The logarithm has actual base two. -/
def CountingConjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → 4 ∣ n →
    (hadamardCount n : ℝ) ≤
      (2 : ℝ) ^ (C * (n : ℝ) * (Real.log (n : ℝ) / Real.log 2))

/-- A restricted matching construction: the first block of rows is fixed and
only the second block is permuted. This gives `m!` distinguishable choices,
sufficient for the full asymptotic counterexample. -/
def doublingMatrix {m : ℕ} (A B : Mat m) (σ : Equiv.Perm (Fin m)) : Mat (m + m) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A B (A.submatrix σ id) (-(B.submatrix σ id)))

/-- The concrete matrix map whose injectivity must be proved. Its output is not
assumed to satisfy the Hadamard condition. -/
def doublingMap (m : ℕ) :
    HadamardMatrices m × HadamardMatrices m × Equiv.Perm (Fin m) → Mat (m + m) :=
  fun x => doublingMatrix x.1.val x.2.1.val x.2.2

end NLA.FR12
