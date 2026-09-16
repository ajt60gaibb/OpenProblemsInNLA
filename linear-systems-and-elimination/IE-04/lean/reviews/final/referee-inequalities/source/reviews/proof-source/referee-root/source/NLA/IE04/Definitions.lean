/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA.

Statement draft for the complete IE-04 Gaussian-smoothed GEPP tail negation.
The generic GEPP definitions below are adapted, without semantic changes, from
the already formalized IE-05 Definitions/Pivot/GEPP source at upstream commit
8f04b905eb2e0827b6b84f37d9d080ae1f05b202. Their original implementation was
AI-assisted work for George Stepaniants. No IE-05 numerical witness is imported.

No proof implementation is included. Two independent statement approvals and
actual Linux declaration elaboration are required before freezing this file.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
open scoped BigOperators NNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory
noncomputable section

namespace NLA.IE04

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev PivotPath (n : ℕ) := Fin n → Fin n

/-- The standard nested product measurable space on the actual n² real entries.
Matrix is a type synonym for the double function space; making this instance
explicit does not change its measurable sets or the Gaussian product law. -/
instance measurableSpaceMat (n : ℕ) : MeasurableSpace (Mat n) :=
  (inferInstance : MeasurableSpace (Fin n → Fin n → ℝ))

/-- The actual induced Euclidean matrix norm, fixed by L2Operator scope. -/
def spectralNorm {n : ℕ} (A : Mat n) : ℝ := ‖A‖

/-- Swap current row positions; partial pivoting never exchanges columns. -/
def rowSwap {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  fun i j => S (Equiv.swap k p i) j

/-- Actual Schur update, padded with zero outside the new active block.
Lean's total division is used only to make this a total function; admissible
paths separately require nonzero pivots. -/
def schurStep {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  let B := rowSwap S k p
  fun i j => if k < i ∧ k < j then
    B i j - (B i k / B k k) * B k j else 0

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

/-- A finite ascending-row scan; an equal magnitude retains the earlier row. -/
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

/-- The true maximum of absolute input entries, as a finite NNReal supremum. -/
def entryMaxNN {n : ℕ} (A : Mat n) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊)

def entryMax {n : ℕ} (A : Mat n) : ℝ := entryMaxNN A

def activeMaxNN {n : ℕ} (S : Mat n) (k : ℕ) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n =>
    if k ≤ ij.1.val ∧ k ≤ ij.2.val then ‖S ij.1 ij.2‖₊ else 0)

def activeMax {n : ℕ} (S : Mat n) (k : ℕ) : ℝ := activeMaxNN S k

/-- The exact n active stages are counted, divided by the original entry max. -/
def growth {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n =>
    activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ) / entryMax A

def firstGrowth {n : ℕ} (A : Mat n) : ℝ := growth A (firstPath A)

/-- A deterministic measurable GEPP tie rule, valid on every nonsingular input.
The frozen Challenge separately proves that firstPath supplies such a rule;
the quantified class cannot silently be empty. -/
def AdmissibleRule {n : ℕ} (rule : Mat n → PivotPath n) : Prop :=
  (∀ A, A.det ≠ 0 → AdmissiblePath A (rule A)) ∧
    Measurable (fun A => growth A (rule A))

/-- n² mutually independent standard real Gaussians, specified by their actual
finite product measure, not by a premise about unspecified random variables. -/
def gaussianMatrix (n : ℕ) : Measure (Mat n) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1))

def smoothedInput {n : ℕ} (center : Mat n) (σ : ℝ) (G : Mat n) : Mat n :=
  center + σ • G

/-- An actual algorithmic tail event on the nonsingular input domain.
Its measurability is a separate exported obligation. Intersecting with this
domain only decreases any total-extension tail event, so a violation here also
violates any such extension without requiring a singular-set nullity premise. -/
def exceedanceEvent {n : ℕ} (center : Mat n) (σ threshold : ℝ)
    (rule : Mat n → PivotPath n) : Set (Mat n) :=
  {G | let A := smoothedInput center σ G
    A.det ≠ 0 ∧ threshold < growth A (rule A)}

/-- The complete original uniform quantifiers and every measurable admissible
tie rule. Real powers are used for the arbitrary real constants c₁,c₂. -/
def UniformExponentialTail : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ n : ℕ, 1 ≤ n → ∀ center : Mat n, spectralNorm center ≤ 1 →
      ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ x : ℝ, 1 ≤ x →
        ∀ rule : Mat n → PivotPath n, AdmissibleRule rule →
          gaussianMatrix n (exceedanceEvent center σ
            (x * ((n : ℝ) / σ) ^ c₁) rule) ≤
              ENNReal.ofReal ((2 : ℝ) ^ (-c₂ * x))

/-- The source's strictly pivoted high-growth matrix, in zero-based indices. -/
def witnessMatrix (n : ℕ) : Mat n :=
  fun i j => if j.val + 1 = n then 1 else
    if i = j then 1 else if j < i then -(1 / 2 : ℝ) else 0

def modelStage (n k : ℕ) : Mat n :=
  fun i j => if k ≤ i.val ∧ k ≤ j.val then
    if j.val + 1 = n then (3 / 2 : ℝ) ^ k else
      if i = j then 1 else if j < i then -(1 / 2 : ℝ) else 0
    else 0

def stageAmplification (n : ℕ) : ℝ := (2 : ℝ) ^ (n + 2)
def boxRadius (n : ℕ) : ℝ := 1 / (2 : ℝ) ^ (n ^ 2 + n + 1)
def probabilityExponent (n : ℕ) : ℕ := n ^ 2 * (n ^ 2 + n + 5)
def growthThreshold (n : ℕ) : ℝ := (3 / 2 : ℝ) ^ (n - 1) / 2

def InWitnessBox {n : ℕ} (A : Mat n) : Prop :=
  ∀ i j, |A i j - witnessMatrix n i j| ≤ boxRadius n

/-- Independent strict-pivot specification along the actual no-swap trajectory.
The final active stage is included; its competitor clause is then empty. -/
def StrictNoSwapPath {n : ℕ} (A : Mat n) : Prop :=
  ∀ k : Fin n,
    0 < trajectory A (noSwapPath n) k.val k k ∧
    ∀ i : Fin n, k < i →
      |trajectory A (noSwapPath n) k.val i k| <
        trajectory A (noSwapPath n) k.val k k

def gaussianBox (n : ℕ) : Set (Mat n) :=
  {G | ∀ i j,
    |G i j - (witnessMatrix n i j - (1 : Mat n) i j)| ≤ boxRadius n}

def contradictionThreshold (n : ℕ) (c₁ : ℝ) : ℝ :=
  (3 / 2 : ℝ) ^ (n - 1) / (2 * (n : ℝ) ^ c₁)

end NLA.IE04
