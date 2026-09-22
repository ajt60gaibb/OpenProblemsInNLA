/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.IE22.Final
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"

#assert_trust kernel NLA.IE22.supremum_semantics
#print axioms NLA.IE22.supremum_semantics
#assert_trust kernel NLA.IE22.constant_semantics
#print axioms NLA.IE22.constant_semantics
#assert_trust kernel NLA.IE22.projection_semantics
#print axioms NLA.IE22.projection_semantics
#assert_trust kernel NLA.IE22.spectral_projection
#print axioms NLA.IE22.spectral_projection
#assert_trust kernel NLA.IE22.gaussian_objective_mean
#print axioms NLA.IE22.gaussian_objective_mean
#assert_trust kernel NLA.IE22.gaussian_objective_variance
#print axioms NLA.IE22.gaussian_objective_variance
#assert_trust kernel NLA.IE22.gaussian_energy_moments
#print axioms NLA.IE22.gaussian_energy_moments
#assert_trust kernel NLA.IE22.bounded_trimming_threshold
#print axioms NLA.IE22.bounded_trimming_threshold
#assert_trust kernel NLA.IE22.threshold_lipschitz
#print axioms NLA.IE22.threshold_lipschitz
#assert_trust kernel NLA.IE22.threshold_grid
#print axioms NLA.IE22.threshold_grid
#assert_trust kernel NLA.IE22.projection_good_event_bound
#print axioms NLA.IE22.projection_good_event_bound
#assert_trust kernel NLA.IE22.deterministic_finite_bound
#print axioms NLA.IE22.deterministic_finite_bound
#assert_trust kernel NLA.IE22.supremum_finite_bound
#print axioms NLA.IE22.supremum_finite_bound
#assert_trust kernel NLA.IE22.deterministic_schedule
#print axioms NLA.IE22.deterministic_schedule
#assert_trust kernel NLA.IE22.universal_squared_rate
#print axioms NLA.IE22.universal_squared_rate
#assert_trust kernel NLA.IE22.uniform_upper_all_rows
#print axioms NLA.IE22.uniform_upper_all_rows
#assert_trust kernel NLA.IE22.spherical_realization_from_finite_bound
#print axioms NLA.IE22.spherical_realization_from_finite_bound
#assert_trust kernel NLA.IE22.high_aspect_near_extremizers
#print axioms NLA.IE22.high_aspect_near_extremizers
#assert_trust kernel NLA.IE22.high_aspect_supremum_limit
#print axioms NLA.IE22.high_aspect_supremum_limit
#assert_trust kernel NLA.IE22.canonical_sharp_constant
#print axioms NLA.IE22.canonical_sharp_constant
