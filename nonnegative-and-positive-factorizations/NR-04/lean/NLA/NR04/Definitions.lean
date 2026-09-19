import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card

set_option autoImplicit false

/-!
# Transparent definitions for the original NR-04 target

Mathematical source: Matthew J. Colbrook, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge, "The nonnegative rank of
the nine-point linear distance matrix", 11 September 2026, Theorem 1 and
Sections 2--5. The reflection upper bound has prior Hrubeš / Gillis--Glineur
attribution, retained in the canonical manuscript and source packet.

Formalization contribution: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, with OpenAI Codex
assistance. This module contains definitions only, no mathematical assumptions,
proof holes, axioms, or imported problem-specific proof modules.

All factors below have arbitrary real entries. The `IsLeast` conclusion in
the separate Challenge records the usual minimum definition of nonnegative
rank without assigning a default value to an empty feasible-width set.
-/

noncomputable section

open scoped BigOperators

namespace NLA.NR04

/-- Entrywise nonnegativity, with no rationality restriction. -/
def EntrywiseNonnegative {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

/-- Exact real nonnegative factorization with the given natural inner dimension. -/
def HasNonnegativeFactorization {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : Prop :=
  ∃ W : Matrix (Fin m) (Fin k) ℝ,
  ∃ H : Matrix (Fin k) (Fin n) ℝ,
    EntrywiseNonnegative W ∧ EntrywiseNonnegative H ∧ W * H = M

/-- The canonical nine-point squared-distance matrix, with zero-based indices. -/
def distanceNine : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j => ((i.val : ℝ) - (j.val : ℝ)) ^ 2

/-- The first three positions of `Fin 9`, without any cyclic relabeling. -/
def firstThree : Fin 3 → Fin 9 := Fin.castAdd 6

/-- Centered real coordinate; index four is the canonical point five. -/
def center (i : Fin 9) : ℝ := (i.val : ℝ) - 4

/-- Exact natural absolute coordinate, computed before coercion to the reals. -/
def label (i : Fin 9) : ℕ := ((i.val : ℤ) - 4).natAbs

/-- The source's explicit nonnegative left factor of inner dimension seven. -/
def upperW : Matrix (Fin 9) (Fin 7) ℝ := fun i r =>
  if r.val < 5 then
    if label i = r.val then 1 else 0
  else if r.val = 5 then 2 * max (center i) 0
  else 2 * max (-center i) 0

/-- The matching explicit right factor; the final two rows reflect signs. -/
def upperH : Matrix (Fin 7) (Fin 9) ℝ := fun r j =>
  if r.val < 5 then ((r.val : ℝ) - (label j : ℝ)) ^ 2
  else if r.val = 5 then 2 * max (-center j) 0
  else 2 * max (center j) 0

/-- Normalized nonnegative columns; this is used only in intermediate geometry. -/
def ColumnStochastic {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  EntrywiseNonnegative M ∧ ∀ j, ∑ i, M i j = 1

/-- The actual set of column vectors, allowing repeated or nonextreme columns. -/
def columnSet {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : Set (Fin m → ℝ) :=
  Set.range fun j => fun i => M i j

/-- The actual convex hull of the columns in the real coordinate vector space. -/
def columnHull {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : Set (Fin m → ℝ) :=
  convexHull ℝ (columnSet M)

/-- The source's `L = aff(columns X)`; no dimension is assumed by this definition. -/
def columnAffineSpan {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    AffineSubspace ℝ (Fin m → ℝ) :=
  affineSpan ℝ (columnSet M)

/-- The genuine section `conv(columns U) ∩ aff(columns X)`. -/
def columnSection {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    Set (Fin N → ℝ) :=
  columnHull U ∩ (columnAffineSpan X : Set (Fin N → ℝ))

end NLA.NR04
