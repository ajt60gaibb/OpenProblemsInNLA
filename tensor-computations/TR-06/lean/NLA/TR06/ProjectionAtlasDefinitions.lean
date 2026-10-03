/-
Proposed statement C only, before implementation or independent approval.
No theorem asserting this proposition is declared here.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology.
-/
import NLA.TR06.Area

set_option autoImplicit false
noncomputable section
open scoped ENNReal MeasureTheory NNReal
open MeasureTheory Set Function Metric

namespace NLA.TR06.Area.Proposed

abbrev Euclid (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- Coordinate restriction, with the Euclidean norm on both spaces. -/
def coordProjection {m N : ℕ} (σ : Fin m ↪ Fin N) (z : Euclid N) : Euclid m :=
  WithLp.toLp 2 (fun i => z (σ i))

/-- An actual embedded smooth manifold, given by smooth embedding charts.
This is an intermediate geometric predicate, not a replacement tensor model. -/
def HasSmoothEmbeddedCharts {N : ℕ} (m : ℕ) (S : Set (Euclid N)) : Prop :=
  ∀ z : S, ∃ c : OpenPartialHomeomorph (Euclid m) S,
    z ∈ c.target ∧
    ContDiffOn ℝ 1 (fun u => (c u).val) c.source ∧
    ∀ u ∈ c.source, Function.Injective (fderiv ℝ (fun v => (c v).val) u)

/-- The projection is injective on an ambient neighborhood within S.
This uses only quantification over real coordinates and a radius, so polynomial
first-order definability requires no separate definability theorem for tangents. -/
def ProjectionLocallyInjectiveSet {m N : ℕ} (S : Set (Euclid N))
    (σ : Fin m ↪ Fin N) : Set (Euclid N) :=
  {z | z ∈ S ∧ ∃ ε : ℝ, 0 < ε ∧ Set.InjOn (coordProjection σ) (S ∩ ball z ε)}

/-- Exact proposed boundary C. This is a proposition definition, not a proved
lemma or an axiom. Every projection family is finite, while branch covers may
be countable. The branch images partition the actual S. -/
def UniformProjectionAtlasStatement : Prop :=
  ∀ (m N : ℕ) (S : Set (Euclid N)), m ≤ N → HasSmoothEmbeddedCharts m S →
  ∃ (K : ℝ≥0)
    (t : (Fin m ↪ Fin N) → ℕ → Set (Euclid m))
    (f : (Fin m ↪ Fin N) → ℕ → Euclid m → Euclid N),
    0 < K ∧
    (∀ σ j, MeasurableSet (t σ j)) ∧
    (∀ σ j, LipschitzOnWith K (f σ j) (t σ j)) ∧
    (∀ σ j, ∀ x ∈ t σ j, coordProjection σ (f σ j x) = x) ∧
    (∀ σ j, f σ j '' t σ j ⊆ ProjectionLocallyInjectiveSet S σ) ∧
    Pairwise (Disjoint on fun q : (Fin m ↪ Fin N) × ℕ => f q.1 q.2 '' t q.1 q.2) ∧
    S = ⋃ σ, ⋃ j, f σ j '' t σ j

#check UniformProjectionAtlasStatement
#print axioms UniformProjectionAtlasStatement

end NLA.TR06.Area.Proposed
