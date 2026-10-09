import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Topology.Order.LocalExtr
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! MD-06: the original limit-one conjecture, with separately named negative
and quantitative resolutions. These are statements only, not proofs.
Exact specification: docs/lean/statements/MD-06/NUMERICAL_TARGETS.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open Filter

namespace NLA.Statements.MD06

abbrev Phase (n : ℕ) := Fin n → Real.Angle

/-- Actual labelled simple graphs; connectedness is not an input restriction. -/
def Cubic {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
by
  classical
  exact G.IsRegularOfDegree 3

/-- Uniform finite counting probability. The target uses only even n >= 4,
where a cycle plus opposite matching gives a cubic graph. -/
noncomputable def Probability (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ := by
  classical
  exact (Fintype.card {G : SimpleGraph (Fin n) // Cubic G ∧ P G} : ℝ) /
    (Fintype.card {G : SimpleGraph (Fin n) // Cubic G} : ℝ)

/-- Each unordered edge is counted exactly once, using the label order. -/
noncomputable def Energy {n : ℕ} (G : SimpleGraph (Fin n)) (theta : Phase n) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then
    1 - Real.Angle.cos (theta i - theta j) else 0

/-- Equality is in the actual circle, across every vertex pair. -/
def Synchronized {n : ℕ} (theta : Phase n) : Prop :=
  ∀ i j, theta i = theta j

def AllSynchronized {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ theta : Phase n, IsLocalMin (Energy G) theta → Synchronized theta

/-- Precisely every even graph size at least four, in order. -/
def Size (k : ℕ) : ℕ := 2 * (k + 2)

/-- Original historical conjecture. Its being refuted does not change its statement. -/
def Target : Prop :=
  Tendsto (fun k => Probability (Size k) AllSynchronized) atTop (nhds (1 : ℝ))

/-- Credited negative answer; this is not substituted for the original Target. -/
def NegativeResolution : Prop :=
  Tendsto (fun k => Probability (Size k) AllSynchronized) atTop (nhds (0 : ℝ))

/-- Exact real derivative coordinates of the periodic energy. -/
noncomputable def Gradient {n : ℕ} (G : SimpleGraph (Fin n))
    (theta : Phase n) (i : Fin n) : ℝ := by
  classical
  exact ∑ j, if G.Adj i j then Real.Angle.sin (theta i - theta j) else 0

/-- Real tangent directions; once per edge, with no factor of two. -/
noncomputable def HessianQuadratic {n : ℕ} (G : SimpleGraph (Fin n))
    (theta : Phase n) (z : Fin n → ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then
    Real.Angle.cos (theta i - theta j) * (z i - z j)^2 else 0

def StableNonsynchronized {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ theta : Phase n,
    IsLocalMin (Energy G) theta ∧ ¬ Synchronized theta ∧
    (∀ i, Gradient G theta i = 0) ∧
    (∀ i j, G.Adj i j → (1 / 32 : ℝ) < Real.Angle.cos (theta i - theta j)) ∧
    ∀ z : Fin n → ℝ, (∑ i, z i) = 0 →
      (1 / 320 : ℝ) * (∑ i, (z i)^2) ≤ HessianQuadratic G theta z

/-- Separate stronger answer with its literal absolute stability constants. -/
def QuantitativeResolution : Prop :=
  Tendsto (fun k => Probability (Size k) StableNonsynchronized) atTop (nhds (1 : ℝ))

#assert_statement Target
#assert_statement NegativeResolution
#assert_statement QuantitativeResolution
#assert_trust kernel Target
#assert_trust kernel NegativeResolution
#assert_trust kernel QuantitativeResolution
#print axioms Target
#print axioms NegativeResolution
#print axioms QuantitativeResolution

end NLA.Statements.MD06
