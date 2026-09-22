/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Original mathematical counterexample and proof: Matthew J. Colbrook.
-/
import NLA.TR27.Counterexample
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"

#assert_trust kernel NLA.TR27.finite_coordinates
#print axioms NLA.TR27.finite_coordinates
#assert_trust kernel NLA.TR27.admissible_geometry
#print axioms NLA.TR27.admissible_geometry
#assert_trust kernel NLA.TR27.cone_projective_membership
#print axioms NLA.TR27.cone_projective_membership
#assert_trust kernel NLA.TR27.projective_cone_rank
#print axioms NLA.TR27.projective_cone_rank
#assert_trust kernel NLA.TR27.rank_minima
#print axioms NLA.TR27.rank_minima
#assert_trust kernel NLA.TR27.projective_affine_border
#print axioms NLA.TR27.projective_affine_border
#assert_trust kernel NLA.TR27.tensor_representatives
#print axioms NLA.TR27.tensor_representatives
#assert_trust kernel NLA.TR27.segre_cone_rank
#print axioms NLA.TR27.segre_cone_rank
#assert_trust kernel NLA.TR27.segre_rank_minimum
#print axioms NLA.TR27.segre_rank_minimum
#assert_trust kernel NLA.TR27.coordinate_transport
#print axioms NLA.TR27.coordinate_transport
#assert_trust kernel NLA.TR27.quotient_semantics
#print axioms NLA.TR27.quotient_semantics
#assert_trust kernel NLA.TR27.homogeneous_parameter_semantics
#print axioms NLA.TR27.homogeneous_parameter_semantics
#assert_trust kernel NLA.TR27.integral_quadratic
#print axioms NLA.TR27.integral_quadratic
#assert_trust kernel NLA.TR27.substitution_integral
#print axioms NLA.TR27.substitution_integral
#assert_trust kernel NLA.TR27.whole_closed_image
#print axioms NLA.TR27.whole_closed_image
#assert_trust kernel NLA.TR27.witness_admissible
#print axioms NLA.TR27.witness_admissible
#assert_trust kernel NLA.TR27.curve_nonzero
#print axioms NLA.TR27.curve_nonzero
#assert_trust kernel NLA.TR27.eight_point_independence
#print axioms NLA.TR27.eight_point_independence
#assert_trust kernel NLA.TR27.witness_three_terms
#print axioms NLA.TR27.witness_three_terms
#assert_trust kernel NLA.TR27.border_curve_semantics
#print axioms NLA.TR27.border_curve_semantics
#assert_trust kernel NLA.TR27.border_two
#print axioms NLA.TR27.border_two
#assert_trust kernel NLA.TR27.square_nine_terms
#print axioms NLA.TR27.square_nine_terms
#assert_trust kernel NLA.TR27.square_not_eight
#print axioms NLA.TR27.square_not_eight
#assert_trust kernel NLA.TR27.projective_counterexample
#print axioms NLA.TR27.projective_counterexample
#assert_trust kernel NLA.TR27.original_conjecture_false
#print axioms NLA.TR27.original_conjecture_false
