import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Powerset
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# TR-07: the original random-column-subset target

The random objects are subsets of column indices, so repeated column values
retain their separate sampling weights. All vector norms are Euclidean.
The probability is an exact finite cardinality ratio on the full collection
of r-element subsets; there is no assumption on support intersections.
-/

noncomputable section

open scoped BigOperators
open Filter

namespace NLA.TR07

abbrev Mat (k n : ℕ) := Matrix (Fin k) (Fin n) ℝ
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Exactly s nonzero signed entries in every column. -/
def SignedSparse {k n : ℕ} (s : ℕ) (M : Mat k n) : Prop := by
  classical
  exact (∀ i j, M i j = -1 ∨ M i j = 0 ∨ M i j = 1) ∧
    ∀ j, (Finset.univ.filter fun i => M i j ≠ 0).card = s

/-- The actual selected rectangular matrix acting on its column coordinates. -/
def selectedAction {k n : ℕ} (M : Mat k n) (I : Finset (Fin n))
    (x : EuclideanSpace ℝ I) : Vec k :=
  WithLp.toLp 2 fun i => ∑ j : I, M i j * x j

/-- Infimum of the selected matrix's norm over its entire Euclidean unit sphere.
Lean's real infimum convention gives zero for the empty unit sphere; the
aspect-ratio hypothesis forces positive sample size eventually, so this
finite-prefix convention has no effect on the asserted limit. -/
def smallestSingular {k n : ℕ} (M : Mat k n) (I : Finset (Fin n)) : ℝ :=
  sInf {y : ℝ | ∃ x : EuclideanSpace ℝ I, ‖x‖ = 1 ∧ y = ‖selectedAction M I x‖}

/-- Probability of the strict tail event under uniform sampling without replacement. -/
def subsetTail {k n : ℕ} (M : Mat k n) (r : ℕ) (η : ℝ) : ℝ := by
  classical
  let samples := (Finset.univ : Finset (Fin n)).powersetCard r
  exact ((samples.filter fun I => η < smallestSingular M I).card : ℝ) / samples.card

/-- Complete canonical asymptotic target. Eventual sparsity makes explicit that
irrelevant dimensions smaller than s impose no restriction on the sequence. -/
def SolvesTR07 : Prop :=
  ∀ (s : ℕ), 2 ≤ s → ∀ (C : ℝ), 1 ≤ C →
  ∀ (r n : ℕ → ℕ), (∀ k, r k ≤ k) → (∀ k, r k ≤ n k) →
    Tendsto (fun k : ℕ => (k : ℝ) / (r k : ℝ)) atTop (nhds C) →
    Tendsto (fun k : ℕ => (n k : ℝ) / (r k : ℝ)) atTop atTop →
    ∀ (M : (k : ℕ) → Mat k (n k)), (∀ᶠ k in atTop, SignedSparse s (M k)) →
    ∀ (η : ℝ), 0 < η →
      Tendsto (fun k => subsetTail (M k) (r k) η) atTop (nhds 0)

end NLA.TR07
