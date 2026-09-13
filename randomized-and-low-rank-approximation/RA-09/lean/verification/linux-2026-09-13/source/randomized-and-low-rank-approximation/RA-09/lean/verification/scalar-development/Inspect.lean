/- Scalar helper inspection only. Reference Challenge is used solely for
type identity; implementation import closure is independently traversed. -/
import NLA.RA09.Scalar
import Challenge
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pairs := [
    (``NLA.RA09.admissible_scalar_consequences, ``NLA.RA09.admissible_scalar_consequences_proved),
    (``NLA.RA09.scalar_branch_certificates, ``NLA.RA09.scalar_branch_certificates_proved),
    (``NLA.RA09.ordered_scalar_certificate, ``NLA.RA09.ordered_scalar_certificate_proved)]
  for (reference, implementation) in pairs do
    let some r := env.find? reference | throwError "Missing reference {reference}"
    let some p := env.find? implementation | throwError "Missing implementation {implementation}"
    unless ← liftTermElabM (Meta.isDefEq r.type p.type) do
      throwError "Frozen type mismatch: {reference} / {implementation}"
    logInfo m!"EXACT_FROZEN_TYPE {reference} = {implementation}"
  let project := fun n : Name => n.toString.startsWith "NLA.RA09." ||
    n.toString.startsWith "_private.NLA.RA09."
  let mut pending := [``NLA.RA09.ordered_scalar_certificate_proved]
  let mut seen : List Name := []
  let mut dependencies : List Name := []
  for _ in [:1000] do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      unless seen.contains name do
        seen := name :: seen
        let some info := env.find? name | throwError "Missing {name}"
        if info.isUnsafe || info.isPartial then throwError "Unsafe/partial {name}"
        for ax in (← liftCoreM <| collectAxioms name) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Unexpected axiom {name}: {ax}"
        let body ← match info.value? (allowOpaque := true) with
          | some b => pure b.getUsedConstants.toList
          | none => match info with
            | .inductInfo _ | .ctorInfo _ | .recInfo _ => pure []
            | _ => throwError "Bodyless {name}"
        let used := info.type.getUsedConstants.toList ++ body
        dependencies := used ++ dependencies
        let ds := used.filter project
        logInfo m!"SCALAR_EDGE {name}: {ds}"
        pending := ds ++ pending
  unless pending.isEmpty do throwError "Incomplete traversal"
  for name in [``NLA.RA09.admissible_scalar_consequences_proved,
      ``NLA.RA09.scalar_branch_certificates_proved, ``NLA.RA09.AdmissibleFunction,
      ``NLA.RA09.scalarAuxiliary, ``NLA.RA09.transferScale, ``NLA.RA09.branchQuadratic,
      ``ConcaveOn] do
    unless dependencies.contains name do throwError "Missing material dependency {name}"
    logInfo m!"RETAINED {name}"
  for suffix in [".NLA.RA09.scalar_cross", ".NLA.RA09.normalized_ordered_certificate"] do
    unless seen.any (fun n => n.toString.endsWith suffix) do
      throwError "Missing material private proof {suffix}"
    logInfo m!"RETAINED_PRIVATE {suffix}"
  for (reference, _) in pairs do
    if dependencies.contains reference then throwError "Reference theorem entered proof closure {reference}"
  logInfo m!"SCALAR_PROJECT_COUNT {seen.length}"

#assert_trust kernel NLA.RA09.admissible_scalar_consequences_proved
#assert_trust kernel NLA.RA09.scalar_branch_certificates_proved
#assert_trust kernel NLA.RA09.ordered_scalar_certificate_proved
#print axioms NLA.RA09.admissible_scalar_consequences_proved
#print axioms NLA.RA09.scalar_branch_certificates_proved
#print axioms NLA.RA09.ordered_scalar_certificate_proved
