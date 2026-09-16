/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
This entrypoint checks all 28 frozen targets. Challenge is never imported.
-/
import NLA.MF12.Realization
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

#assert_trust kernel NLA.MF12.family_growth_is_maximum
#print axioms NLA.MF12.family_growth_is_maximum
#assert_trust kernel NLA.MF12.pair_word_norms
#print axioms NLA.MF12.pair_word_norms
#assert_trust kernel NLA.MF12.entry_maximum_norm_comparison
#print axioms NLA.MF12.entry_maximum_norm_comparison
#assert_trust kernel NLA.MF12.tensor_norm_comparison
#print axioms NLA.MF12.tensor_norm_comparison
#assert_trust kernel NLA.MF12.tensor_word_identity
#print axioms NLA.MF12.tensor_word_identity
#assert_trust kernel NLA.MF12.fractional_parameters
#print axioms NLA.MF12.fractional_parameters
#assert_trust kernel NLA.MF12.fractional_projection
#print axioms NLA.MF12.fractional_projection
#assert_trust kernel NLA.MF12.jordan_two_power
#print axioms NLA.MF12.jordan_two_power
#assert_trust kernel NLA.MF12.compressed_powers
#print axioms NLA.MF12.compressed_powers
#assert_trust kernel NLA.MF12.loss_gain_bounds
#print axioms NLA.MF12.loss_gain_bounds
#assert_trust kernel NLA.MF12.telescoping_budget
#print axioms NLA.MF12.telescoping_budget
#assert_trust kernel NLA.MF12.compressed_product_formula
#print axioms NLA.MF12.compressed_product_formula
#assert_trust kernel NLA.MF12.compressed_product_bound
#print axioms NLA.MF12.compressed_product_bound
#assert_trust kernel NLA.MF12.fractional_powers_entry_bound
#print axioms NLA.MF12.fractional_powers_entry_bound
#assert_trust kernel NLA.MF12.gap_decomposition
#print axioms NLA.MF12.gap_decomposition
#assert_trust kernel NLA.MF12.reset_product_factorization
#print axioms NLA.MF12.reset_product_factorization
#assert_trust kernel NLA.MF12.fractional_all_word_upper
#print axioms NLA.MF12.fractional_all_word_upper
#assert_trust kernel NLA.MF12.logarithmic_gap_bounds
#print axioms NLA.MF12.logarithmic_gap_bounds
#assert_trust kernel NLA.MF12.bernoulli_loss
#print axioms NLA.MF12.bernoulli_loss
#assert_trust kernel NLA.MF12.lower_word_exact
#print axioms NLA.MF12.lower_word_exact
#assert_trust kernel NLA.MF12.fractional_lower_all_lengths
#print axioms NLA.MF12.fractional_lower_all_lengths
#assert_trust kernel NLA.MF12.fractional_growth_estimates
#print axioms NLA.MF12.fractional_growth_estimates
#assert_trust kernel NLA.MF12.roots_of_polynomial_growth
#print axioms NLA.MF12.roots_of_polynomial_growth
#assert_trust kernel NLA.MF12.jordan_entries
#print axioms NLA.MF12.jordan_entries
#assert_trust kernel NLA.MF12.jordan_growth_estimates
#print axioms NLA.MF12.jordan_growth_estimates
#assert_trust kernel NLA.MF12.integer_family_growth
#print axioms NLA.MF12.integer_family_growth
#assert_trust kernel NLA.MF12.fractional_tensor_growth
#print axioms NLA.MF12.fractional_tensor_growth
#assert_trust kernel NLA.MF12.realizes_every_nonnegative_exponent
#print axioms NLA.MF12.realizes_every_nonnegative_exponent
