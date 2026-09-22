/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.IE21.FiniteSize
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"

#assert_trust kernel NLA.IE21.surface_probability
#print axioms NLA.IE21.surface_probability
#assert_trust kernel NLA.IE21.gaussian_surface_correspondence
#print axioms NLA.IE21.gaussian_surface_correspondence
#assert_trust kernel NLA.IE21.product_row_semantics
#print axioms NLA.IE21.product_row_semantics
#assert_trust kernel NLA.IE21.independent_row_transport
#print axioms NLA.IE21.independent_row_transport
#assert_trust kernel NLA.IE21.matrix_semantics
#print axioms NLA.IE21.matrix_semantics
#assert_trust kernel NLA.IE21.deletion_minimum
#print axioms NLA.IE21.deletion_minimum
#assert_trust kernel NLA.IE21.deletion_zero_cases
#print axioms NLA.IE21.deletion_zero_cases
#assert_trust kernel NLA.IE21.finite_trimming_semantics
#print axioms NLA.IE21.finite_trimming_semantics
#assert_trust kernel NLA.IE21.directional_minimum
#print axioms NLA.IE21.directional_minimum
#assert_trust kernel NLA.IE21.statistics_measurable
#print axioms NLA.IE21.statistics_measurable
#assert_trust kernel NLA.IE21.gaussian_constant
#print axioms NLA.IE21.gaussian_constant
#assert_trust kernel NLA.IE21.spherical_moments
#print axioms NLA.IE21.spherical_moments
#assert_trust kernel NLA.IE21.spherical_quadratic_mgf
#print axioms NLA.IE21.spherical_quadratic_mgf
#assert_trust kernel NLA.IE21.spherical_gaussian_trimming
#print axioms NLA.IE21.spherical_gaussian_trimming
#assert_trust kernel NLA.IE21.pointwise_trim_concentration
#print axioms NLA.IE21.pointwise_trim_concentration
#assert_trust kernel NLA.IE21.sphere_net
#print axioms NLA.IE21.sphere_net
#assert_trust kernel NLA.IE21.covariance_concentration
#print axioms NLA.IE21.covariance_concentration
#assert_trust kernel NLA.IE21.uniform_trim_concentration
#print axioms NLA.IE21.uniform_trim_concentration
#assert_trust kernel NLA.IE21.finite_size_bound
#print axioms NLA.IE21.finite_size_bound
#assert_trust kernel NLA.IE21.finite_size_independent_rows
#print axioms NLA.IE21.finite_size_independent_rows
#assert_trust kernel NLA.IE21.aspect_schedule
#print axioms NLA.IE21.aspect_schedule
#assert_trust kernel NLA.IE21.spherical_ratio_limit
#print axioms NLA.IE21.spherical_ratio_limit
#assert_trust kernel NLA.IE21.original_random_row_limit
#print axioms NLA.IE21.original_random_row_limit
