import NLA.TR06.Rectangular
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace NLA.TR06.Proposed

/-- C1 maps send Lebesgue null subsets of their finite-dimensional Euclidean
source to null sets for source-dimensional normalized Hausdorff measure. -/
def ContDiffNullImageStatement : Prop :=
  ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] (f : E → F) (s : Set E),
    ContDiff ℝ 1 f → (volume : Measure E) s = 0 →
    (μHE[Module.finrank ℝ E] : Measure F) (f '' s) = 0

#check ContDiffNullImageStatement
end NLA.TR06.Proposed
