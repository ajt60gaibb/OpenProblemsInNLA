import NLA.TR06.Area

noncomputable section
open scoped ENNReal MeasureTheory
open MeasureTheory
namespace NLA.TR06.IndependentAreaReview
theorem exact_reviewed_target {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (c : DecompositionChart d n r)
    (s : Set (EuclideanSpace ℝ (Fin (expectedDimension d n r))))
    (hs : MeasurableSet s) (hsub : s ⊆ c.chart.source) :
    (μHE[expectedDimension d n r] : Measure (Tensor ℝ d n))
      ((fun v => (c.chart v).val) '' s) =
    ∫⁻ v in s,
      ENNReal.ofReal ((fderiv ℝ (fun w => (c.chart w).val) v).toLinearMap.normDet) := by
  exact NLA.TR06.induced_volume_chart c s hs hsub
#print axioms exact_reviewed_target
#assert_trust kernel exact_reviewed_target
end NLA.TR06.IndependentAreaReview
