import NLA.IE22.GaussianVariance
noncomputable section
open MeasureTheory ProbabilityTheory
open NLA.IE21 NLA.IE22
example (θ : ℝ) (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d)
    (B : Mat m d) (t : ℝ) (ht : 0 ≤ t) :
    MemLp (projectedObjective θ B t) 2 (stdGaussian (Space d)) ∧
    Var[projectedObjective θ B t; stdGaussian (Space d)] ≤
      4 * t * operatorNorm B ^ 2 / m :=
  gaussian_objective_variance θ m d hm hd B t ht
#print axioms NLA.IE22.variance_eq_half_pair_energy
#print axioms NLA.IE22.gaussian_density_hasDerivAt
#print axioms NLA.IE22.gaussian_density_tendsto_atTop
#print axioms NLA.IE22.gaussian_density_tendsto_atBot
#print axioms NLA.IE22.gaussian_density_first_moment_integrable
#print axioms NLA.IE22.gaussian_density_right_first_moment
#print axioms NLA.IE22.gaussian_density_left_first_moment
#print axioms NLA.IE22.gaussian_setIntegral_density
#print axioms NLA.IE22.gaussian_right_first_moment
#print axioms NLA.IE22.gaussian_left_first_moment
#print axioms NLA.IE22.gaussian_crossing_kernel
#print axioms NLA.IE22.gaussian_crossing_weight_measurable
#print axioms NLA.IE22.measurable_gaussianCrossingWeight
#print axioms NLA.IE22.gaussian_crossing_kernel_lintegral
#print axioms NLA.IE22.gaussian_crossing_energy
#print axioms NLA.IE22.gaussian_pair_energy_lintegral
#print axioms NLA.IE22.gaussian_variance_le_of_crossing_bound
#print axioms NLA.IE22.gaussian_crossing_square_energy
#print axioms NLA.IE22.gaussian_poincare_of_interval_energy
#print axioms NLA.IE22.integral_square_le_mass
#print axioms NLA.IE22.interval_energy_of_absolutelyContinuous
#print axioms NLA.IE22.affineHinge_continuous
#print axioms NLA.IE22.affineHingeDerivative_measurable
#print axioms NLA.IE22.affineHinge_absolutelyContinuous
#print axioms NLA.IE22.affineHinge_hasDerivAt_of_ne
#print axioms NLA.IE22.affineHinge_ae_hasDerivAt
#print axioms NLA.IE22.affineHingeDerivative_bound
#print axioms NLA.IE22.affineHingeSum_continuous
#print axioms NLA.IE22.affineHingeSumDerivative_measurable
#print axioms NLA.IE22.affineHinge_norm_le
#print axioms NLA.IE22.affineHingeSum_norm_le
#print axioms NLA.IE22.affineHingeSum_memLp
#print axioms NLA.IE22.affineHingeSumDerivative_bound
#print axioms NLA.IE22.affineHingeSum_absolutelyContinuous
#print axioms NLA.IE22.affineHingeSum_ae_hasDerivAt
#print axioms NLA.IE22.affineHingeSum_gaussian_variance
#print axioms NLA.IE22.matrix_adjoint_coordinate
#print axioms NLA.IE22.activeRowVector_norm_sq_le
#print axioms NLA.IE22.objectivePartial_square_sum_le
#print axioms NLA.IE22.projectedObjective_continuous
#print axioms NLA.IE22.projectedObjective_norm_le
#print axioms NLA.IE22.projectedObjective_memLp
#print axioms NLA.IE22.activeRowVector_measurable
#print axioms NLA.IE22.objectivePartial_measurable
#print axioms NLA.IE22.activeRowVector_abs_le
#print axioms NLA.IE22.objectivePartial_norm_le
#print axioms NLA.IE22.matrixMap_update
#print axioms NLA.IE22.objective_fiber_eq_hingeSum
#print axioms NLA.IE22.objective_partial_fiber_eq
#print axioms NLA.IE22.objective_fiber_variance_le
#print axioms NLA.IE22.objectivePartial_square_norm_le
#print axioms NLA.IE22.gaussian_objective_variance
