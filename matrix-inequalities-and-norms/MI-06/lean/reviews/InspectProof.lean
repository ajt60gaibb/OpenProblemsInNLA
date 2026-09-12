/- Read-only proof-term inspection; this is diagnostic evidence, not an extra axiom. -/
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
    let some info := env.find? current | throwError "Missing declaration: {current}"
    let some value := info.value? (allowOpaque := true)
      | throwError "Missing proof body: {current}"
    let some next := value.getUsedConstants.find? (fun n => n.toString == target)
      | throwError "Proof body {current} does not directly retain {target}"
    logInfo m!"RETAINED: {current} -> {next}"
    current := next
  let some info := env.find? current | throwError "Missing final certificate"
  let some value := info.value? (allowOpaque := true)
    | throwError "Missing certificate body"
  logInfo m!"CERTIFICATE CONSTANTS: {value.getUsedConstants}"
  logInfo m!"CERTIFICATE PROOF TERM: {value}"

#print axioms NLA.MI06.counterexample
#print axioms NLA.MI06.not_dominationConjecture
