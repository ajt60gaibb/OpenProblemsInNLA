import NLA.IE22.GaussianEnergy
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory NLA.IE21 NLA.IE22
open scoped ENNReal BigOperators RealInnerProductSpace
example (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (B : Mat m d) :
    MemLp (projectedEnergy B) 2 (stdGaussian (Space d)) ∧
    (∫ g, projectedEnergy B g ∂stdGaussian (Space d)) = Matrix.trace (gramMatrix B) / m ∧
    Var[projectedEnergy B; stdGaussian (Space d)] =
      2 * Matrix.trace (gramMatrix B * gramMatrix B) / (m : ℝ) ^ 2 := NLA.IE22.gaussian_energy_moments m d hm hd B

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
