/- Independent final referee's proof-term checks. Diagnostic only; no theorem replacement. -/
import Solution
import Lean.Util.FoldConsts

set_option pp.proofs true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut current := ``NLA.MI06.not_dominationConjecture
  for target in [
      "NLA.MI06.not_dominationConjecture_proved",
      "NLA.MI06.counterexample_proved",
      "_private.NLA.MI06.Proof.0.NLA.MI06.scalar_coefficient_gap",
      "_private.NLA.MI06.Proof.0.NLA.MI06.sqrt_two_lt_three_halves",
      "_private.NLA.MI06.Proof.0.NLA.MI06.scalar_squared_gap"] do
    let some ci := env.find? current | throwError "Missing declaration: {current}"
    let some body := ci.value? (allowOpaque := true) | throwError "No proof: {current}"
    let some next := body.getUsedConstants.find? (fun n => n.toString == target)
      | throwError "Missing direct certificate dependency: {current} -> {target}"
    logInfo m!"RETAINED_CERTIFICATE_EDGE: {current} -> {next}"
    current := next
  let some ci := env.find? current | throwError "Missing scalar certificate"
  let some body := ci.value? (allowOpaque := true) | throwError "No scalar proof"
  unless body.getUsedConstants.any
      (fun n => n.toString == "LeanCert.Validity.verify_strict_upper_bound_dyadic_checked") do
    throwError "Scalar proof does not retain the checked LeanCert theorem"
  logInfo m!"KERNEL_CERTIFICATE_CONSTANTS: {body.getUsedConstants}"
  logInfo m!"KERNEL_CERTIFICATE_BODY: {body}"
  for name in [``NLA.MI06.witness_moduli_proved,
      ``NLA.MI06.two_vector_orthogonal_proved,
      ``NLA.MI06.witness_quadratic_bounds_proved,
      ``NLA.MI06.counterexample_proved] do
    let some ci := env.find? name | throwError "Missing reviewed proof {name}"
    let some body := ci.value? (allowOpaque := true) | throwError "No proof {name}"
    logInfo m!"PROOF_DIRECT_CONSTANTS {name}: {body.getUsedConstants}"

#assert_trust kernel NLA.MI06.modulus_eq_sqrt
#assert_trust kernel NLA.MI06.witness_moduli
#assert_trust kernel NLA.MI06.two_vector_orthogonal
#assert_trust kernel NLA.MI06.witness_quadratic_bounds
#assert_trust kernel NLA.MI06.counterexample
#assert_trust kernel NLA.MI06.not_dominationConjecture

#print axioms NLA.MI06.modulus_eq_sqrt
#print axioms NLA.MI06.witness_moduli
#print axioms NLA.MI06.two_vector_orthogonal
#print axioms NLA.MI06.witness_quadratic_bounds
#print axioms NLA.MI06.counterexample
#print axioms NLA.MI06.not_dominationConjecture
