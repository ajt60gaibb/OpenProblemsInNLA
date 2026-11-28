/-
  MI20/AxiomAudit.lean
  ====================
  Author:      Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
  Purpose:     Verify that every major theorem in the 13-module MI-20 Lean 4 + Mathlib
               formalization (40 V4 theorems + 23 V5 theorems + 10 V5-Blitz theorems = 73 audited theorems)
               depends ONLY on Lean's three standard axioms
               `[propext, Classical.choice, Quot.sound]`, with zero `sorry` and zero
               custom axioms.
-/

import MI20

#print axioms MI20.prop0_subgradient_bound
#print axioms MI20.lemma1_universal_rank_deficiency
#print axioms MI20.lemma2_full_rank_sum
#print axioms MI20.lemma2_same_dim_full_rank_sum
#print axioms MI20.lemma3_polar_optimality
#print axioms MI20.lemma3_kernel_map
#print axioms MI20.psdPow_mono_of_posSemidef
#print axioms MI20.lemma4a_rank_one_smoothness
#print axioms MI20.lemma4b_kernel_lifting
#print axioms MI20.prop5_superquadratic_obstruction
#print axioms MI20.theorem1_strict_hierarchy
#print axioms MI20.theorem1_no_finite_extremizer
#print axioms MI20.schattenNorm_sq_le_trace_mul_rpow
#print axioms MI20.theorem3_universal_2x2_collapse
#print axioms MI20.theorem3_exact_p32
#print axioms MI20.theorem4_witness_p32
#print axioms MI20.theorem5_psd_reformulation
#print axioms MI20.theorem5_povm_reformulation
#print axioms MI20.theorem6_interp_from_one
#print axioms MI20.theorem6_p2_upper_bound
#print axioms MI20.universal_commutator_identity
#print axioms MI20.universal_commutator_theorem
#print axioms MI20.power_variance_lemma
#print axioms MI20.top_eigenspace_spectral_dichotomy
#print axioms MI20.universal_algebraic_upper_bound
#print axioms MI20.universal_bound_p43_m2
#print axioms MI20.universal_bound_p32_m2
#print axioms MI20.universal_quadratic_log_bound
#print axioms MI20.exists_negative_flux_eigenvector
#print axioms MI20.universal_sharp_one_line_bound
#print axioms MI20.sharp_one_line_cap_p43_m2
#print axioms MI20.sharp_one_line_cap_p32_m2
#print axioms MI20.sharp_one_line_p2_limit_frobenius
#print axioms MI20.universal_two_function_bound
#print axioms MI20.two_function_regime1_bound
#print axioms MI20.two_function_regime2_bound
#print axioms MI20.superexponential_p2_collapse_bound
#print axioms MI20.two_function_cap_p32_m2
#print axioms MI20.two_function_cap_p43_m2
#print axioms MI20.bessel_two_line_identity_p43
#print axioms MI20.quantitative_power_variance_lemma
#print axioms MI20.universal_spectral_gap_theorem
#print axioms MI20.bogomolny_sos_identity_p43
#print axioms MI20.vacuum_defect_cubic_identity_p43
#print axioms MI20.bogomolny_sos_identity_p32
#print axioms MI20.pinching_decomposition_p43
#print axioms MI20.pinching_decomposition_p32
#print axioms MI20.action_ray_convexity_p43
#print axioms MI20.action_ray_convexity_p32
#print axioms MI20.negative_trace_drift_2x2_p43
#print axioms MI20.sum_trace_negSpectralProj_le
#print axioms MI20.master_trace_implies_no_global_solution
#print axioms MI20.spectral_pencil_factorization_p43
#print axioms MI20.spectral_pencil_factorization_p32
#print axioms MI20.spectral_pencil_disjoint_kernels_p43
#print axioms MI20.spectral_pencil_rhp_roots_p43
#print axioms MI20.lemma0_lambda_sigma_minus_gt_one
#print axioms MI20.spectral_pencil_rho4_lt_half
#print axioms MI20.spectral_pencil_rho3_lt_half
#print axioms MI20.two_vector_cancellation_identity_p43
#print axioms MI20.spectral_gap_cert_mu0_p43
#print axioms MI20.spectral_gap_cert_interval_p43
#print axioms MI20.fifth_universal_quadratic_moment_identity
#print axioms MI20.universal_phi_psd_rigidity
#print axioms MI20.third_root_harmonic_mean_bound
#print axioms MI20.third_root_pencil_rho4_lt_eighth
#print axioms MI20.pinching_second_variation_pos_p43
#print axioms MI20.pinching_second_variation_pos_p32
#print axioms MI20.hessian_det_pos_2x2_p43
#print axioms MI20.master_trace_2x2_p43
#print axioms MI20.master_trace_2x2_p32
#print axioms MI20.euler_betti_root_identity
#print axioms MI20.hessian_sign_pairs_all_p
