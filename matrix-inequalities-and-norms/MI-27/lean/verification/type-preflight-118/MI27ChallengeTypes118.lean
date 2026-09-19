import Challenge
import Lean

open Lean Elab Command

run_cmd do
  let info ← getConstInfo `NLA.MI27.half_coefficient_positive
  logInfo ("TYPEJSON NLA.MI27.half_coefficient_positive " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.half_coefficient_positive " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.spectral_function_semantics
  logInfo ("TYPEJSON NLA.MI27.spectral_function_semantics " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.spectral_function_semantics " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.normalize_positive_pair
  logInfo ("TYPEJSON NLA.MI27.normalize_positive_pair " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.normalize_positive_pair " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.positive_trace_operator_bound
  logInfo ("TYPEJSON NLA.MI27.positive_trace_operator_bound " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.positive_trace_operator_bound " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.positive_commutator_trace_bound
  logInfo ("TYPEJSON NLA.MI27.positive_commutator_trace_bound " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.positive_commutator_trace_bound " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.positive_part_variational
  logInfo ("TYPEJSON NLA.MI27.positive_part_variational " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.positive_part_variational " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.positive_part_trace_lipschitz
  logInfo ("TYPEJSON NLA.MI27.positive_part_trace_lipschitz " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.positive_part_trace_lipschitz " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.unitary_flow_semantics
  logInfo ("TYPEJSON NLA.MI27.unitary_flow_semantics " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.unitary_flow_semantics " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.hockey_stick_unitary_lipschitz
  logInfo ("TYPEJSON NLA.MI27.hockey_stick_unitary_lipschitz " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.hockey_stick_unitary_lipschitz " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.uniform_hockey_stick_cutoff
  logInfo ("TYPEJSON NLA.MI27.uniform_hockey_stick_cutoff " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.uniform_hockey_stick_cutoff " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.relative_entropy_finite_hockey_stick
  logInfo ("TYPEJSON NLA.MI27.relative_entropy_finite_hockey_stick " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.relative_entropy_finite_hockey_stick " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.weighted_entropy_finite_kernel
  logInfo ("TYPEJSON NLA.MI27.weighted_entropy_finite_kernel " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.weighted_entropy_finite_kernel " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.kernel_integrals
  logInfo ("TYPEJSON NLA.MI27.kernel_integrals " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.kernel_integrals " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.kernel_entropy_mass_bound
  logInfo ("TYPEJSON NLA.MI27.kernel_entropy_mass_bound " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.kernel_entropy_mass_bound " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.entropy_trajectory_lipschitz
  logInfo ("TYPEJSON NLA.MI27.entropy_trajectory_lipschitz " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.entropy_trajectory_lipschitz " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.entropy_unitary_mix_derivative
  logInfo ("TYPEJSON NLA.MI27.entropy_unitary_mix_derivative " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.entropy_unitary_mix_derivative " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.skew_commutator_trace_norm
  logInfo ("TYPEJSON NLA.MI27.skew_commutator_trace_norm " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.skew_commutator_trace_norm " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.hermitian_trace_norm_witness
  logInfo ("TYPEJSON NLA.MI27.hermitian_trace_norm_witness " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.hermitian_trace_norm_witness " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.logarithmic_commutator_dual_bound
  logInfo ("TYPEJSON NLA.MI27.logarithmic_commutator_dual_bound " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.logarithmic_commutator_dual_bound " ++ reprStr info.levelParams)

run_cmd do
  let info ← getConstInfo `NLA.MI27.logarithmic_commutator_bound
  logInfo ("TYPEJSON NLA.MI27.logarithmic_commutator_bound " ++ reprStr info.type)
  logInfo ("LEVELJSON NLA.MI27.logarithmic_commutator_bound " ++ reprStr info.levelParams)

