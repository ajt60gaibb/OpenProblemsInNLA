import NLA.TR27.Geometry
import NLA.TR27.Independence

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27

example :
    (∀ j, (homogeneousCoordinate j).IsHomogeneous 12) ∧
    (∀ w : ParameterSpace, homogeneousMap w = 0 ↔ w = 0) ∧
    Set.range homogeneousMap = parameterizedCone := NLA.TR27.homogeneous_parameter_semantics

example : witnessVariety.Admissible := NLA.TR27.witness_admissible

example (k : ℕ) (hk : k ≤ 8)
    (p : Fin k → ℙ ℂ Space) (hp : ∀ i, p i ∈ witnessVariety.points)
    (hi : Function.Injective p) : Projectivization.Independent p :=
  NLA.TR27.eight_point_independence k hk p hp hi

#print axioms NLA.TR27.homogeneousCoordinate_isHomogeneous
#print axioms NLA.TR27.homogeneousMap_eq_zero_iff
#print axioms NLA.TR27.homogeneous_parameter_semantics
#print axioms NLA.TR27.substitution_homogeneous
#print axioms NLA.TR27.substitution_homogeneousComponent
#print axioms NLA.TR27.witnessIdeal_isHomogeneous
#print axioms NLA.TR27.witnessIdeal_isPrime
#print axioms NLA.TR27.sourceCurve_span
#print axioms NLA.TR27.curve_mem_cone
#print axioms NLA.TR27.witness_cone_span
#print axioms NLA.TR27.witness_admissible
#print axioms NLA.TR27.coefficientFunctional
#print axioms NLA.TR27.coefficientFunctional_apply
#print axioms NLA.TR27.coefficientFunctional_sourceUnit
#print axioms NLA.TR27.coefficientFunctional_some
#print axioms NLA.TR27.coefficientFunctional_none
#print axioms NLA.TR27.tangentFactor
#print axioms NLA.TR27.tangentPolynomial
#print axioms NLA.TR27.tangentFactor_degree
#print axioms NLA.TR27.tangentFactor_coeff_zero
#print axioms NLA.TR27.tangentPolynomial_degree
#print axioms NLA.TR27.tangentPolynomial_degree_of_none
#print axioms NLA.TR27.tangentPolynomial_coeff_one
#print axioms NLA.TR27.tangentPolynomial_eval
#print axioms NLA.TR27.tangentPolynomial_annihilates
#print axioms NLA.TR27.tangent_not_sum
#print axioms NLA.TR27.separatingFactor
#print axioms NLA.TR27.separatingPolynomial
#print axioms NLA.TR27.separatingFactor_degree
#print axioms NLA.TR27.separatingPolynomial_degree
#print axioms NLA.TR27.separatingPolynomial_eval_self
#print axioms NLA.TR27.separatingPolynomial_eval_other
#print axioms NLA.TR27.separatingPolynomial_annihilates
#print axioms NLA.TR27.source_curve_independent
#print axioms NLA.TR27.tangent_not_span
#print axioms NLA.TR27.center_not_span
#print axioms NLA.TR27.projected_curve_independent
#print axioms NLA.TR27.projective_curve_representation
#print axioms NLA.TR27.eight_point_independence
end NLA.TR27
