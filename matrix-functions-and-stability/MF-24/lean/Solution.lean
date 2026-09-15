/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.

The independently approved Challenge environment is not imported. All 22
frozen mathematical targets are checked here for kernel-only dependencies.
-/
import NLA.MF24.Unbounded
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

#assert_trust kernel NLA.MF24.family_dimensions
#assert_trust kernel NLA.MF24.source_words_eq_height_shifts
#assert_trust kernel NLA.MF24.height_shift_powers
#assert_trust kernel NLA.MF24.family_nilpotent_nonnegative
#assert_trust kernel NLA.MF24.polynomial_degree_evaluation
#assert_trust kernel NLA.MF24.polynomial_entries
#assert_trust kernel NLA.MF24.gram_continuant
#assert_trust kernel NLA.MF24.gram_transfer
#assert_trust kernel NLA.MF24.transfer_bridge
#assert_trust kernel NLA.MF24.family_gram_charpoly
#assert_trust kernel NLA.MF24.gram_singular_bridge
#assert_trust kernel NLA.MF24.family_super_identical
#assert_trust kernel NLA.MF24.first_row_and_nonzero
#assert_trust kernel NLA.MF24.polynomial_numerator_bound
#assert_trust kernel NLA.MF24.residue_geometry
#assert_trust kernel NLA.MF24.residue_weight_bounds
#assert_trust kernel NLA.MF24.polynomial_denominator_energy
#assert_trust kernel NLA.MF24.polynomial_denominator_bound
#assert_trust kernel NLA.MF24.polynomial_norm_ratio
#assert_trust kernel NLA.MF24.finite_rational_family_ratio
#assert_trust kernel NLA.MF24.arbitrarily_large_ratios
#assert_trust kernel NLA.MF24.no_uniform_comparison

#print axioms NLA.MF24.family_dimensions
#print axioms NLA.MF24.source_words_eq_height_shifts
#print axioms NLA.MF24.height_shift_powers
#print axioms NLA.MF24.family_nilpotent_nonnegative
#print axioms NLA.MF24.polynomial_degree_evaluation
#print axioms NLA.MF24.polynomial_entries
#print axioms NLA.MF24.gram_continuant
#print axioms NLA.MF24.gram_transfer
#print axioms NLA.MF24.transfer_bridge
#print axioms NLA.MF24.family_gram_charpoly
#print axioms NLA.MF24.gram_singular_bridge
#print axioms NLA.MF24.family_super_identical
#print axioms NLA.MF24.first_row_and_nonzero
#print axioms NLA.MF24.polynomial_numerator_bound
#print axioms NLA.MF24.residue_geometry
#print axioms NLA.MF24.residue_weight_bounds
#print axioms NLA.MF24.polynomial_denominator_energy
#print axioms NLA.MF24.polynomial_denominator_bound
#print axioms NLA.MF24.polynomial_norm_ratio
#print axioms NLA.MF24.finite_rational_family_ratio
#print axioms NLA.MF24.arbitrarily_large_ratios
#print axioms NLA.MF24.no_uniform_comparison
