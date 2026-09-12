/- Independent read-only inspection of fresh root-referee artifacts. -/
import Solution
import Lean.Util.FoldConsts

set_option pp.proofs true
set_option pp.explicit true

#print NLA.MI06.DominationConjecture
#print NLA.MI06.matrixModulus
#print NLA.MI06.symmetricModulus
#print NLA.MI06.squaredLength
#print NLA.MI06.quadraticForm
#check @NLA.MI06.modulus_eq_sqrt
#check @NLA.MI06.witness_moduli
#check @NLA.MI06.two_vector_orthogonal
#check @NLA.MI06.witness_quadratic_bounds
#check @NLA.MI06.counterexample
#check @NLA.MI06.not_dominationConjecture

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending : List Name := [``NLA.MI06.not_dominationConjecture]
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
      if dependency.toString.startsWith "NLA.MI06." ||
          dependency.toString.startsWith "_private.NLA.MI06.Proof." then
        logInfo m!"PROJECT PROOF EDGE: {current} -> {dependency}"
        pending := dependency :: pending
    if current.toString.endsWith ".NLA.MI06.scalar_squared_gap" then
      unless body.getUsedConstants.any (fun n =>
          n.toString == "LeanCert.Validity.verify_strict_upper_bound_dyadic_checked") do
        throwError "The actual scalar proof does not retain the checked LeanCert theorem"
      certificateSeen := true
      logInfo m!"ACTUAL RETAINED CERTIFICATE: {body}"
  unless certificateSeen do
    throwError "The final public negation does not retain the scalar certificate"
  logInfo m!"PASS: inspected {visited.length} reachable project declarations from the public negation"

#print axioms NLA.MI06.not_dominationConjecture
