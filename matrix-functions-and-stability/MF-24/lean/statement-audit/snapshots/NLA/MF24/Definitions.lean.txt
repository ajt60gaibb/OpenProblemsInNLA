/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization draft.

Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
This file contains definitions only. It does not assert a proof or transfer
original mathematical authorship to the formalization author.
-/
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Data.List.GetD
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

set_option autoImplicit false

namespace NLA.MF24

open Polynomial
open scoped BigOperators

noncomputable section

abbrev Square (N : ℕ) := Matrix (Fin N) (Fin N) ℂ

abbrev EuclideanVector (N : ℕ) := EuclideanSpace ℂ (Fin N)

/-- Genuine induced Euclidean operator norm, explicitly through the continuous
linear map. No default entrywise matrix norm is used. -/
def spectralNorm {N : ℕ} (A : Square N) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) A‖

/-- Actual ordered singular values, including multiplicities and zeros.
Mathlib uses indices beginning at zero; exactly N indices are retained here. -/
def singularValue {N : ℕ} (A : Square N) (j : Fin N) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues j.val

def scalarShift {N : ℕ} (A : Square N) (z : ℂ) : Square N :=
  A - z • (1 : Square N)

def gram {N : ℕ} (A : Square N) : Square N := A.conjTranspose * A

def SuperIdentical {N : ℕ} (A B : Square N) : Prop :=
  ∀ z : ℂ, ∀ j : Fin N,
    singularValue (scalarShift A z) j = singularValue (scalarShift B z) j

/-- Actual evaluation of a complex polynomial in a complex matrix. -/
def polyEval {N : ℕ} (A : Square N) (p : ℂ[X]) : Square N :=
  Polynomial.aeval A p

/-- The full original dimension-independent comparison assertion. -/
def UniformComparison : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ A B : Square N,
    SuperIdentical A B → ∀ p : ℂ[X],
      spectralNorm (polyEval A p) ≤ C * spectralNorm (polyEval B p)

def dimension (m : ℕ) : ℕ := (m + 1) ^ 2

def stride (m : ℕ) : ℕ := m + 2

/-- The source motif has length m for the required range m ≥ 2. -/
def motif (m : ℕ) (t : ℝ) : List ℝ := t :: List.replicate (m - 1) 1

def inverseBridges (m : ℕ) (t : ℝ) : List ℝ :=
  (List.replicate (m - 1) (t⁻¹ :: motif m t)).flatten

/-- Source order is left to right in the edge word, not in the later transfer
product. The unit bridge is first for X and last for Y. -/
def sourceWordX (m : ℕ) (t : ℝ) : List ℝ :=
  motif m t ++ [1] ++ motif m t ++ inverseBridges m t

def sourceWordY (m : ℕ) (t : ℝ) : List ℝ :=
  motif m t ++ inverseBridges m t ++ [1] ++ motif m t

/-- A real upper shift, embedded into complex matrices. The default zero is
used only outside a supplied word; the family word lengths are an explicit
proof obligation. Row r uses edge number r in zero-based list indexing. -/
def wordShift (word : List ℝ) (N : ℕ) : Square N :=
  fun r s => if r.val + 1 = s.val then (word.getD r.val 0 : ℂ) else 0

def matrixX (m : ℕ) (t : ℝ) : Square (dimension m) :=
  wordShift (sourceWordX m t) (dimension m)

def matrixY (m : ℕ) (t : ℝ) : Square (dimension m) :=
  wordShift (sourceWordY m t) (dimension m)

/-- The exact source prefix heights, with v=q(m+1)+s. -/
def heightX (m v : ℕ) : ℕ :=
  (if 1 ≤ v % (m + 1) then 1 else 0) +
  (if 1 ≤ v / (m + 1) then 1 else 0)

def heightY (m v : ℕ) : ℕ :=
  (if 1 ≤ v % (m + 1) then 1 else 0) +
  (if v / (m + 1) = m then 1 else 0)

/-- Natural powers and a positive denominator avoid integer powers in the
definition. Equality with the source-word shifts is required separately. -/
def heightShift {N : ℕ} (h : Fin N → ℕ) (t : ℝ) : Square N :=
  fun r s => if r.val + 1 = s.val then
    ((t ^ h s / t ^ h r : ℝ) : ℂ) else 0

def testPolynomial (m : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.Icc 1 m, (X : ℂ[X]) ^ (stride m * j)

/-- ρ=|z|² as a complex scalar in the exact transfer identities. -/
def shiftRadiusSq (z : ℂ) : ℂ := (Complex.normSq z : ℂ)

def transferMatrix (u ρ a : ℂ) : Square 2 :=
  !![u + a, -ρ * a; 1, 0]

def transferInitial (u : ℂ) : Fin 2 → ℂ := ![u, 1]

/-- Later edges act on the left; list reversal is essential. -/
def transferProduct (u ρ : ℂ) (word : List ℝ) : Square 2 :=
  (word.reverse.map (fun w => transferMatrix u ρ ((w : ℂ) ^ 2))).prod

/-- Algebraic first coordinate, without a conjugate transpose. -/
def transferValue (u ρ : ℂ) (word : List ℝ) : ℂ :=
  (Matrix.mulVec (transferProduct u ρ word) (transferInitial u)) 0

/-- Actual leading Gram-plus-ηI determinant. At order j, exactly the first
j−1 edges of the original word can occur. The zero-dimensional determinant
is the ordinary determinant 1, not a separately stipulated recurrence value. -/
def leadingGramDet (word : List ℝ) (z η : ℂ) (j : ℕ) : ℂ :=
  (gram (scalarShift (wordShift word j) z) + η • (1 : Square j)).det

/-- Every vertex in a residue class is retained. -/
def residueClass (m : ℕ) (c : Fin (stride m)) : Finset (Fin (dimension m)) :=
  Finset.univ.filter (fun v => v.val % stride m = c.val)

def heightWeight (m : ℕ) (t : ℝ) (v : Fin (dimension m)) : ℝ :=
  t ^ heightY m v.val

def inverseHeightWeight (m : ℕ) (t : ℝ) (v : Fin (dimension m)) : ℝ :=
  (heightWeight m t v)⁻¹

end
end NLA.MF24
