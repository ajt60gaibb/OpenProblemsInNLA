import NLA.TR06.RankOneCharts
import NLA.TR06.ClosedFibers

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
namespace NLA.TR06.Proposed

/-- Relative properness of actual addition on the COMPLETE closed cone product,
including every zero summand, over an ambient open good set. -/
def CompactAdditionPreimagesOn {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (U : Set (Tensor ℝ d n)) : Prop :=
  ∀ K : Set (Tensor ℝ d n), IsCompact K → K ⊆ U →
    IsCompact {a : Fin r → Tensor ℝ d n |
      a ∈ closedRankOneProduct ℝ d n r ∧ (∑ i, a i) ∈ K}

/-- Every actual length-r decomposition above U has exact rank and uniqueness.
This is an intermediate certificate premise, never a final TR-06 assumption. -/
def IdentifiableAdditionOn {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (U : Set (Tensor ℝ d n)) : Prop :=
  ∀ A ∈ U, (∃ a : Fin r → Tensor ℝ d n, Decomposes a A) →
    A ∈ identifiableRealSet d n r

/-- Properness controls all nearby decompositions in the WHOLE ordered
rank-one product. Exact rank at A rules out zero summands in limiting fibers. -/
def AdditionFiberNeighborhoodStatement : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ) (r : ℕ) (U : Set (Tensor ℝ d n)),
    IsOpen U → CompactAdditionPreimagesOn (r := r) U →
    ∀ (A : Tensor ℝ d n), A ∈ U → ExactRank r A →
    ∀ V : Set (OrderedRankOne d n r), IsOpen V →
      (∀ a : OrderedRankOne d n r, (∑ i, a.val i) = A → a ∈ V) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ a : OrderedRankOne d n r,
        dist (∑ i, a.val i) A < ε → a ∈ V

/-- An actual Segre immersion plus complete relative properness and uniqueness
constructs a frozen smooth chart with target open in the WHOLE identifiable
set, through the specified ordered decomposition. No image-openness premise. -/
def SmoothChartOfProperImmersionStatement : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ) (r : ℕ), 0 < d →
    ∀ (U : Set (Tensor ℝ d n)), IsOpen U →
      IdentifiableAdditionOn (r := r) U → CompactAdditionPreimagesOn (r := r) U →
    ∀ (q₀ : Fin r → TensorIndex d n) (z : OrderedPivotData q₀),
      (∀ i, (z i).1 ≠ 0) → pivotSum q₀ z ∈ U →
      Function.Injective (fderiv ℝ (pivotSum q₀) z) →
      ∃ c : SmoothDecompositionChart d n r,
        ∃ u : EuclideanSpace ℝ (Fin (expectedDimension d n r)),
          u ∈ c.chart.source ∧ (c.chart u).val = pivotSum q₀ z ∧
          c.summands u = orderedTensorFromPivotData q₀ z ∧
          ∀ v ∈ c.chart.source, (c.chart v).val ∈ U

/-- Assembly on every actual good identifiable tensor. All three intermediate
certificate hypotheses must subsequently be discharged from genericity. -/
def SmoothRegularOnProperImmersionStatement : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ) (r : ℕ), 0 < d →
    ∀ (U : Set (Tensor ℝ d n)), IsOpen U →
      IdentifiableAdditionOn (r := r) U → CompactAdditionPreimagesOn (r := r) U →
      (∀ (q₀ : Fin r → TensorIndex d n) (z : OrderedPivotData q₀),
        (∀ i, (z i).1 ≠ 0) → pivotSum q₀ z ∈ U →
        Function.Injective (fderiv ℝ (pivotSum q₀) z)) →
      U ∩ identifiableRealSet d n r ⊆ smoothRegularSet d n r

#check AdditionFiberNeighborhoodStatement
#check SmoothChartOfProperImmersionStatement
#check SmoothRegularOnProperImmersionStatement
end NLA.TR06.Proposed
