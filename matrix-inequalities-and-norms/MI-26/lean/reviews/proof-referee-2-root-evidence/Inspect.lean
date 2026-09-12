/- Independent read-only inspection of fresh root-referee artifacts. -/
import Solution
import Lean.Util.FoldConsts

set_option pp.proofs true
set_option pp.explicit true

#print NLA.MI26.AdmissibleFunction
#print NLA.MI26.functionalCalculus
#print NLA.MI26.SubadditivityConjecture
#print NLA.MI26.functionalCalculus_eq_spectral_proved
#check @NLA.MI26.admissibleFunction_iff
#check @NLA.MI26.functionalCalculus_eq_spectral
#check @NLA.MI26.functionalCalculus_congr_nonneg
#check @NLA.MI26.quadratic_cfc
#check @NLA.MI26.witness_data
#check @NLA.MI26.counterexample
#check @NLA.MI26.not_subadditivityConjecture

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending : List Name := [``NLA.MI26.not_subadditivityConjecture]
  let mut visited : List Name := []
  let mut certificateSeen := false
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    if visited.contains current then continue
    visited := current :: visited
    let some info := env.find? current | throwError "Missing declaration {current}"
    let some body := info.value? (allowOpaque := true) | continue
    for dependency in body.getUsedConstants do
      if dependency.toString.startsWith "NLA.MI26." ||
          dependency.toString.startsWith "_private.NLA.MI26.Proof." then
        logInfo m!"PROJECT PROOF EDGE: {current} -> {dependency}"
        pending := dependency :: pending
    if current.toString == "NLA.MI26.witness_positive" then
      unless body.getUsedConstants.any (fun n =>
          n.toString == "LeanCert.Validity.verify_strict_upper_bound_dyadic_checked") do
        throwError "The actual scalar proof does not retain the checked LeanCert theorem"
      certificateSeen := true
      logInfo m!"ACTUAL RETAINED CERTIFICATE: {body}"
  unless certificateSeen do
    throwError "The final public negation does not retain the scalar certificate"
  logInfo m!"PASS: inspected {visited.length} reachable project declarations from the public negation"

#print axioms NLA.MI26.not_subadditivityConjecture
