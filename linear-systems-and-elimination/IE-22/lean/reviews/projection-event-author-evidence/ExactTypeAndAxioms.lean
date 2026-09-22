import NLA.IE22.ProjectionEvent
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory NLA.IE21 NLA.IE22
open scoped ENNReal BigOperators RealInnerProductSpace
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m d r : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hr : 1 ≤ r) (B : Mat m d)
    (hrows : ∀ i, ‖matrixRow B i‖ ≤ 1)
    (hop : operatorNorm B ^ 2 ≤ (m : ℝ) / ((r : ℝ) + 1))
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    MeasurableSet (ProjectionGood θ B δ) ∧
    (stdGaussian (Space d)).real (ProjectionGood θ B δ)ᶜ ≤ projectionFailure θ d r δ := NLA.IE22.projection_good_event_bound θ hθ m d r hm hd hr B hrows hop δ hδ

#print axioms NLA.IE22.measureReal_abs_deviation_le
#print axioms NLA.IE22.measureReal_upper_tail_le_variance
#print axioms NLA.IE22.gaussian_radius_lower_tail
#print axioms NLA.IE22.continuous_projectedObjective
#print axioms NLA.IE22.projectionGood_measurable
#print axioms NLA.IE22.projection_event_probability_of_bounds
#print axioms NLA.IE22.projection_good_event_of_energy_variance
#print axioms NLA.IE22.row_inner_square_sum_le
#print axioms NLA.IE22.gaussian_projectedEnergy_variance_le
#print axioms NLA.IE22.projection_good_event_bound
