/- Independent read-only final proof-term inspection. -/
import Solution
import Lean.Util.FoldConsts

set_option pp.proofs true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut current := ``NLA.MI26.not_subadditivityConjecture
  for target in ["NLA.MI26.not_subadditivityConjecture_proved",
      "NLA.MI26.counterexample_proved", "NLA.MI26.witness_positive"] do
    let some info := env.find? current | throwError "Missing {current}"
    let some body := info.value? (allowOpaque := true) | throwError "No body: {current}"
    let some next := body.getUsedConstants.find? (fun n => n.toString == target)
      | throwError "Missing direct retained edge: {current} -> {target}"
    logInfo m!"RETAINED_KERNEL_EDGE: {current} -> {next}"
    current := next
  let some info := env.find? current | throwError "Missing scalar certificate"
  let some body := info.value? (allowOpaque := true) | throwError "No scalar body"
  unless body.getUsedConstants.any
      (fun n => n.toString == "LeanCert.Validity.verify_strict_upper_bound_dyadic_checked") do
    throwError "Certificate did not retain the actual checked LeanCert theorem"
  logInfo m!"CERTIFICATE_BODY: {body}"
  for name in [``NLA.MI26.functionalCalculus_eq_spectral_proved,
      ``NLA.MI26.functionalCalculus_congr_nonneg_proved,
      ``NLA.MI26.quadratic_cfc_proved,
      ``NLA.MI26.admissibleFunction_iff_proved,
      ``NLA.MI26.witness_data_proved,
      ``NLA.MI26.counterexample_proved] do
    let some info := env.find? name | throwError "Missing {name}"
    let some body := info.value? (allowOpaque := true) | throwError "No body: {name}"
    logInfo m!"DIRECT_DEPENDENCIES {name}: {body.getUsedConstants}"
    if name == ``NLA.MI26.functionalCalculus_eq_spectral_proved then
      unless body.getUsedConstants.any (fun n => n == ``Matrix.IsHermitian.cfc_eq) do
        throwError "The generic spectral bridge did not retain genuine Mathlib cfc_eq"

#assert_trust kernel NLA.MI26.admissibleFunction_iff
#assert_trust kernel NLA.MI26.functionalCalculus_eq_spectral
#assert_trust kernel NLA.MI26.functionalCalculus_congr_nonneg
#assert_trust kernel NLA.MI26.quadratic_cfc
#assert_trust kernel NLA.MI26.witness_data
#assert_trust kernel NLA.MI26.counterexample
#assert_trust kernel NLA.MI26.not_subadditivityConjecture

#print axioms NLA.MI26.admissibleFunction_iff
#print axioms NLA.MI26.functionalCalculus_eq_spectral
#print axioms NLA.MI26.functionalCalculus_congr_nonneg
#print axioms NLA.MI26.quadratic_cfc
#print axioms NLA.MI26.witness_data
#print axioms NLA.MI26.counterexample
#print axioms NLA.MI26.not_subadditivityConjecture
