/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization draft.
Original mathematics: Matthew J. Colbrook, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom.
This file defines the complete canonical objects only; it proves no result.
-/
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
open scoped BigOperators Classical

namespace NLA.MF12
noncomputable section

abbrev Square (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev EuclideanVector (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The genuine induced Euclidean operator norm, not an entrywise matrix norm. -/
def spectralNorm {d : ℕ} (A : Square d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖

/-- Chronological convention: later factors act on the left. -/
def matrixProduct {d : ℕ} (w : List (Square d)) : Square d := w.reverse.prod

/-- All genuine length-n family products. Repeated factors are unrestricted. -/
def wordNorms {d : ℕ} (M : Finset (Square d)) (n : ℕ) : Set ℝ :=
  {r | ∃ w : List (Square d), w.length = n ∧
    (∀ A ∈ w, A ∈ M) ∧ r = spectralNorm (matrixProduct w)}

/-- The finite maximum is a separate exported attainment obligation. -/
def familyGrowth {d : ℕ} (M : Finset (Square d)) (n : ℕ) : ℝ := sSup (wordNorms M n)

def pairFamily {d : ℕ} (A P : Square d) : Finset (Square d) := {A, P}

/-- false selects A and true selects P, with chronological list order. -/
def binaryProduct {d : ℕ} (A P : Square d) (w : List Bool) : Square d :=
  matrixProduct (w.map (fun b => cond b P A))

/-- Genuine maximum absolute entry, with 0 included for zero dimension.
For positive dimensions an actual matrix entry attains it, as separately required. -/
def entryMax {d : ℕ} (A : Square d) : ℝ :=
  sSup ({0} ∪ Set.range (fun ij : Fin d × Fin d => |A ij.1 ij.2|))

/-- The actual Kronecker matrix in canonical Fin(d*e) coordinates. -/
def tensor {d e : ℕ} (A : Square d) (B : Square e) : Square (d * e) :=
  (Matrix.kronecker A B).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

def baseLambda : ℝ := 1 / 4

def baseMu (α : ℝ) : ℝ := Real.rpow baseLambda (1 - α)

def jordanTwo (t : ℝ) : Square 2 := !![t, t; 0, t]

/-- Colbrook's unchanged six-dimensional block-diagonal matrix. -/
def fractionalMatrix (α : ℝ) : Square 6 :=
  !![1, 0, 0, 0, 0, 0;
     0, baseLambda, baseLambda, 0, 0, 0;
     0, 0, baseLambda, 0, 0, 0;
     0, 0, 0, baseMu α, baseMu α, 0;
     0, 0, 0, 0, baseMu α, 0;
     0, 0, 0, 0, 0, 1]

def sourceV : Matrix (Fin 6) (Fin 2) ℝ :=
  !![1, 0; 0, 0; 1, 0; 0, 0; 0, 1; 0, 1]

def sourceU : Matrix (Fin 2) (Fin 6) ℝ :=
  !![1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1]

def resetMatrix : Square 6 := sourceV * sourceU

def loss (q : ℕ) : ℝ := (q : ℝ) * baseLambda ^ q

def gain (α : ℝ) (q : ℕ) : ℝ := (q : ℝ) * baseMu α ^ q

/-- Actual compressed power, not a recurrence surrogate. -/
def compressed (α : ℝ) (q : ℕ) : Square 2 :=
  sourceU * fractionalMatrix α ^ q * sourceV

def compressedProduct (α : ℝ) (qs : List ℕ) : Square 2 :=
  matrixProduct (qs.map (compressed α))

def tailWeight (qs : List ℕ) (i : ℕ) : ℝ :=
  ((qs.drop (i + 1)).map (fun q => 1 - loss q)).prod

def diagonalBudget (qs : List ℕ) : ℝ :=
  (qs.map (fun q => 1 - loss q)).prod

def offDiagonalBudget (α : ℝ) (qs : List ℕ) : ℝ :=
  ∑ i ∈ Finset.range qs.length, gain α (qs.getD i 0) * tailWeight qs i

/-- Consecutive gap blocks are separated by a single reset, including zero gaps. -/
def gapWord (qs : List ℕ) : List Bool :=
  ((qs.map (fun q => List.replicate q false)).intersperse [true]).flatten

def fractionalPowerBound (α : ℝ) : ℝ := (1 - baseMu α)⁻¹

def fractionalLower (α : ℝ) : ℝ := Real.rpow baseLambda α / 10

def fractionalUpper (α : ℝ) : ℝ := 1728 * fractionalPowerBound α ^ 2

def chosenGap (n : ℕ) : ℕ := Nat.log 4 n

def chosenCount (n : ℕ) : ℕ := n / (chosenGap n + 1)

def chosenRemainder (n : ℕ) : ℕ := n - chosenCount n * (chosenGap n + 1)

/-- An exact-length word for every n; the first three positive lengths use A^n. -/
def lowerWord (n : ℕ) : List Bool :=
  if n < 4 then List.replicate n false else
    (List.replicate (chosenCount n)
      (List.replicate (chosenGap n) false ++ [true])).flatten ++
      List.replicate (chosenRemainder n) false

def upperShift (d : ℕ) : Square d :=
  fun r s => if r.val + 1 = s.val then 1 else 0

/-- Order m+1, with eigenvalue one and superdiagonal ones. -/
def jordanMatrix (m : ℕ) : Square (m + 1) := 1 + upperShift (m + 1)

def jordanLower (m : ℕ) : ℝ := if m = 0 then 1 else ((m : ℝ) ^ m)⁻¹

def liftedA (α : ℝ) (m : ℕ) : Square (6 * (m + 1)) :=
  tensor (fractionalMatrix α) (jordanMatrix m)

def liftedP (m : ℕ) : Square (6 * (m + 1)) :=
  tensor resetMatrix (jordanMatrix m)

def liftedLower (α : ℝ) (m : ℕ) : ℝ :=
  fractionalLower α * jordanLower m / (6 * ((m + 1 : ℕ) : ℝ))

def liftedUpper (α : ℝ) (m : ℕ) : ℝ :=
  (6 * ((m + 1 : ℕ) : ℝ)) * fractionalUpper α * ((m + 1 : ℕ) : ℝ)

end
end NLA.MF12
