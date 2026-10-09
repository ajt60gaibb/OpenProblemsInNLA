/-
Released under the Apache 2.0 license; see LICENSE.

The generic matrix, row-swap, Schur-recursion, pivot-path, entry-maximum and
Gaussian-product definitions are adapted from NLA.IE04.Definitions at repository
commit 286d8768fbd9a69264daa88e285680293db29837. That implementation credits
George Stepaniants (Department of Computing and Mathematical Sciences,
California Institute of Technology) and earlier AI-assisted IE-05 work.
This IE-06 adaptation is AI-assisted statement formalization, not a proof of
John Urschel's manuscript. See source/source-lock.json and reviews/.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped NNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace NLA.IE06

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev PivotPath (n : ℕ) := Fin n → Fin n

instance measurableSpaceMat (n : ℕ) : MeasurableSpace (Mat n) :=
  (inferInstance : MeasurableSpace (Fin n → Fin n → ℝ))

/-- Swap current row positions; columns are never permuted. -/
def rowSwap {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  fun i j => S (Equiv.swap k p i) j

/-- Exact Schur update, with zeros outside the next active block.
Total division only extends the function to invalid paths; admissibility
separately requires every denominator to be nonzero. -/
def schurStep {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  let B := rowSwap S k p
  fun i j => if k < i ∧ k < j then
    B i j - (B i k / B k k) * B k j else 0

/-- Stage zero is the input; stage k follows k eliminations. -/
def trajectory {n : ℕ} (A : Mat n) (path : PivotPath n) : ℕ → Mat n
  | 0 => A
  | k + 1 => if h : k < n then
      schurStep (trajectory A path k) ⟨k, h⟩ (path ⟨k, h⟩) else 0

/-- Every maximum-magnitude active-column pivot is eligible, including ties. -/
def AdmissiblePivot {n : ℕ} (S : Mat n) (k p : Fin n) : Prop :=
  k ≤ p ∧ S p k ≠ 0 ∧ ∀ i, k ≤ i → |S i k| ≤ |S p k|

def AdmissiblePath {n : ℕ} (A : Mat n) (path : PivotPath n) : Prop :=
  ∀ k, AdmissiblePivot (trajectory A path k.val) k (path k)

/-- Maximum absolute input entry; the empty-dimensional maximum is zero. -/
def entryMaxNN {n : ℕ} (A : Mat n) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊)

def entryMax {n : ℕ} (A : Mat n) : ℝ := entryMaxNN A

/-- Only entries in the active trailing block count. -/
def activeMaxNN {n : ℕ} (S : Mat n) (k : ℕ) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n =>
    if k ≤ ij.1.val ∧ k ≤ ij.2.val then ‖S ij.1 ij.2‖₊ else 0)

/-- All n active stages, including the input and the last scalar complement,
normalized by the original entry maximum. It is used only on admissible paths
of nonsingular positive-dimensional inputs in the probability event. -/
def growth {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n =>
    activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ) / entryMax A

/-- The actual law of n² mutually independent N(0,1) entries; gaussianReal's
second argument is the variance. There is no conditioning on pivot success. -/
def gaussianMatrix (n : ℕ) : Measure (Mat n) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1))

/-- A bad path exists exactly when the universal bound over all admissible
tie choices fails. Singular inputs are excluded, as in the canonical problem.
The explicit dimension guard makes this event empty for n = 0 at every t. -/
def exceedanceEvent (n : ℕ) (t : ℝ) : Set (Mat n) :=
  {A | 0 < n ∧ A.det ≠ 0 ∧ ∃ path : PivotPath n,
    AdmissiblePath A path ∧ t < growth A path}

#assert_trust kernel rowSwap
#assert_trust kernel schurStep
#assert_trust kernel trajectory
#assert_trust kernel AdmissiblePivot
#assert_trust kernel AdmissiblePath
#assert_trust kernel entryMaxNN
#assert_trust kernel entryMax
#assert_trust kernel activeMaxNN
#assert_trust kernel growth
#assert_trust kernel gaussianMatrix
#assert_trust kernel exceedanceEvent

end NLA.IE06
