import NLA.IE21.SphericalTrimming

#print axioms NLA.IE21.integral_abs_le_sqrt_second_moment
#print axioms NLA.IE21.gaussian_radius_deviation_bound
#print axioms NLA.IE21.spherical_gaussian_coupling_distance
#print axioms NLA.IE21.spherical_gaussian_trimming

open MeasureTheory ProbabilityTheory Set
namespace NLA.IE21
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (n : ℕ) (hn : 2 ≤ n) (x : Space n) (hx : ‖x‖ = 1) :
    |populationTrim θ (sphereLaw n) (directionalEnergy x) - gaussianTrim θ| ≤ Real.sqrt (2 / (n : ℝ)) :=
  spherical_gaussian_trimming θ hθ n hn x hx
end NLA.IE21
