import NLA.IE22.ProjectionEvent
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
open NLA.IE21 NLA.IE22

example (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (B : Mat m d) :
    MemLp (projectedEnergy B) 2 (stdGaussian (Space d)) ∧
    (∫ g, projectedEnergy B g ∂stdGaussian (Space d)) = Matrix.trace (gramMatrix B) / m ∧
    Var[projectedEnergy B; stdGaussian (Space d)] =
      2 * Matrix.trace (gramMatrix B * gramMatrix B) / (m : ℝ) ^ 2 := NLA.IE22.gaussian_energy_moments m d hm hd B

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m d r : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hr : 1 ≤ r) (B : Mat m d)
    (hrows : ∀ i, ‖matrixRow B i‖ ≤ 1)
    (hop : operatorNorm B ^ 2 ≤ (m : ℝ) / ((r : ℝ) + 1))
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    MeasurableSet (ProjectionGood θ B δ) ∧
    (stdGaussian (Space d)).real (ProjectionGood θ B δ)ᶜ ≤ projectionFailure θ d r δ := NLA.IE22.projection_good_event_bound θ hθ m d r hm hd hr B hrows hop δ hδ

#print axioms NLA.IE22.gaussian_inner_pow_integrable

#print axioms NLA.IE22.gaussian_inner_even_moment_general

#print axioms NLA.IE22.gaussian_inner_sq_mean

#print axioms NLA.IE22.gaussian_inner_fourth_mean

#print axioms NLA.IE22.gaussian_inner_sq_mul_sq_integrable

#print axioms NLA.IE22.gaussian_inner_cross_fourth

#print axioms NLA.IE22.gram_trace_eq_row_sum

#print axioms NLA.IE22.row_gram_eq_inner

#print axioms NLA.IE22.gram_sq_trace_eq_row_inner_sum

#print axioms NLA.IE22.projectedEnergy_eq_row_sum

#print axioms NLA.IE22.gaussian_projectedEnergy_memLp

#print axioms NLA.IE22.gaussian_projectedEnergy_mean

#print axioms NLA.IE22.gaussian_projectedEnergy_second_moment

#print axioms NLA.IE22.gaussian_energy_moments

#print axioms NLA.IE22.gram_trace_nonneg

#print axioms NLA.IE22.gram_trace_le_rows

#print axioms NLA.IE22.gaussian_projectedEnergy_mean_le_one

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
