import NLA.MI27.LogarithmicCommutator

/- Full unchanged original MI-27 target, with twenty independently frozen contracts.
The Solution environment never imports Challenge.
Analytic resolution: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with Codex assistance.
Prior mathematical, library and code authorship is retained in the source files.
-/
set_option leancert.trust "kernel"

#print axioms NLA.MI27.half_coefficient_positive
#assert_trust kernel NLA.MI27.half_coefficient_positive

#print axioms NLA.MI27.spectral_function_semantics
#assert_trust kernel NLA.MI27.spectral_function_semantics

#print axioms NLA.MI27.normalize_positive_pair
#assert_trust kernel NLA.MI27.normalize_positive_pair

#print axioms NLA.MI27.positive_trace_operator_bound
#assert_trust kernel NLA.MI27.positive_trace_operator_bound

#print axioms NLA.MI27.positive_commutator_trace_bound
#assert_trust kernel NLA.MI27.positive_commutator_trace_bound

#print axioms NLA.MI27.positive_part_variational
#assert_trust kernel NLA.MI27.positive_part_variational

#print axioms NLA.MI27.positive_part_trace_lipschitz
#assert_trust kernel NLA.MI27.positive_part_trace_lipschitz

#print axioms NLA.MI27.unitary_flow_semantics
#assert_trust kernel NLA.MI27.unitary_flow_semantics

#print axioms NLA.MI27.hockey_stick_unitary_lipschitz
#assert_trust kernel NLA.MI27.hockey_stick_unitary_lipschitz

#print axioms NLA.MI27.uniform_hockey_stick_cutoff
#assert_trust kernel NLA.MI27.uniform_hockey_stick_cutoff

#print axioms NLA.MI27.relative_entropy_finite_hockey_stick
#assert_trust kernel NLA.MI27.relative_entropy_finite_hockey_stick

#print axioms NLA.MI27.weighted_entropy_finite_kernel
#assert_trust kernel NLA.MI27.weighted_entropy_finite_kernel

#print axioms NLA.MI27.kernel_integrals
#assert_trust kernel NLA.MI27.kernel_integrals

#print axioms NLA.MI27.kernel_entropy_mass_bound
#assert_trust kernel NLA.MI27.kernel_entropy_mass_bound

#print axioms NLA.MI27.entropy_trajectory_lipschitz
#assert_trust kernel NLA.MI27.entropy_trajectory_lipschitz

#print axioms NLA.MI27.entropy_unitary_mix_derivative
#assert_trust kernel NLA.MI27.entropy_unitary_mix_derivative

#print axioms NLA.MI27.skew_commutator_trace_norm
#assert_trust kernel NLA.MI27.skew_commutator_trace_norm

#print axioms NLA.MI27.hermitian_trace_norm_witness
#assert_trust kernel NLA.MI27.hermitian_trace_norm_witness

#print axioms NLA.MI27.logarithmic_commutator_dual_bound
#assert_trust kernel NLA.MI27.logarithmic_commutator_dual_bound

#print axioms NLA.MI27.logarithmic_commutator_bound
#assert_trust kernel NLA.MI27.logarithmic_commutator_bound
