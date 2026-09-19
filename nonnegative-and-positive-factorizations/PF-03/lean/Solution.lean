/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; substantial Codex assistance.
Original mathematics and exact seed: Sidney Holden, Center for Computational
Biology, Flatiron Institute, Simons Foundation. Component credits are retained.

Aggregate for all 25 exact frozen PF03 contracts. Its presence is not execution
or review evidence. See STATE.json and formalization.yaml for current gates.
The independently trusted Challenge module is deliberately not imported.
-/
import NLA.PF03.Counterexample

set_option autoImplicit false
set_option leancert.trust "kernel"

#print axioms NLA.PF03.alpha_certificate
#assert_trust kernel NLA.PF03.alpha_certificate
#print axioms NLA.PF03.cubic_eval_operations
#assert_trust kernel NLA.PF03.cubic_eval_operations
#print axioms NLA.PF03.cubic_eval_injective
#assert_trust kernel NLA.PF03.cubic_eval_injective
#print axioms NLA.PF03.seed_orthogonal
#assert_trust kernel NLA.PF03.seed_orthogonal
#print axioms NLA.PF03.seed_quadratic_form
#assert_trust kernel NLA.PF03.seed_quadratic_form
#print axioms NLA.PF03.seed_local_data
#assert_trust kernel NLA.PF03.seed_local_data
#print axioms NLA.PF03.local_quadratic_kernel
#assert_trust kernel NLA.PF03.local_quadratic_kernel
#print axioms NLA.PF03.rational_ray_zero
#assert_trust kernel NLA.PF03.rational_ray_zero
#print axioms NLA.PF03.triangle_certificate
#assert_trust kernel NLA.PF03.triangle_certificate
#print axioms NLA.PF03.cross_cone_certificate
#assert_trust kernel NLA.PF03.cross_cone_certificate
#print axioms NLA.PF03.positive_slice_certificate
#assert_trust kernel NLA.PF03.positive_slice_certificate
#print axioms NLA.PF03.cone_quadratic_zeros
#assert_trust kernel NLA.PF03.cone_quadratic_zeros
#print axioms NLA.PF03.cone_rational_zeros
#assert_trust kernel NLA.PF03.cone_rational_zeros
#print axioms NLA.PF03.cone_pointed
#assert_trust kernel NLA.PF03.cone_pointed
#print axioms NLA.PF03.one_variable_projection
#assert_trust kernel NLA.PF03.one_variable_projection
#print axioms NLA.PF03.rational_projection
#assert_trust kernel NLA.PF03.rational_projection
#print axioms NLA.PF03.rational_cone_halfspaces
#assert_trust kernel NLA.PF03.rational_cone_halfspaces
#print axioms NLA.PF03.pointed_halfspaces_injective
#assert_trust kernel NLA.PF03.pointed_halfspaces_injective
#print axioms NLA.PF03.gram_factor_transport
#assert_trust kernel NLA.PF03.gram_factor_transport
#print axioms NLA.PF03.trace_obstruction
#assert_trust kernel NLA.PF03.trace_obstruction
#print axioms NLA.PF03.no_rational_factor
#assert_trust kernel NLA.PF03.no_rational_factor
#print axioms NLA.PF03.padded_real_factor
#assert_trust kernel NLA.PF03.padded_real_factor
#print axioms NLA.PF03.cp_zero_diagonal_frontier
#assert_trust kernel NLA.PF03.cp_zero_diagonal_frontier
#print axioms NLA.PF03.pf03_counterexample
#assert_trust kernel NLA.PF03.pf03_counterexample
#print axioms NLA.PF03.canonical_negative_answer
#assert_trust kernel NLA.PF03.canonical_negative_answer
