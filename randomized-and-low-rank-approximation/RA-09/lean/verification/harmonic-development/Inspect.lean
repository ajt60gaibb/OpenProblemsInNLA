/- Harmonic helper inspection only. The reference Challenge is used solely
for type comparison and must not enter the implementation proof closure. -/
import NLA.RA09.Harmonic
import Challenge
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let reference := ``NLA.RA09.harmonic_constraint
  let implementation := ``NLA.RA09.harmonic_constraint_proved
  let some r := env.find? reference | throwError "Missing reference"
  let some p := env.find? implementation | throwError "Missing implementation"
  unless ← liftTermElabM (Meta.isDefEq r.type p.type) do
    throwError "Frozen harmonic type mismatch"
  logInfo m!"EXACT_FROZEN_TYPE {reference} = {implementation}"
  let project := fun n : Name => n.toString.startsWith "NLA.RA09." ||
    n.toString.startsWith "_private.NLA.RA09."
  let mut pending := [implementation]
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
        logInfo m!"HARMONIC_EDGE {name}: {ds}"
        pending := ds ++ pending
  unless pending.isEmpty do throwError "Incomplete traversal"
  for name in [``NLA.RA09.outerSquare, ``NLA.RA09.outerSquare_mulVec,
      ``NLA.RA09.diagonal_outer_quadratic, ``Matrix.PosSemidef,
      ``Matrix.PosSemidef.diag_nonneg, ``Matrix.PosSemidef.dotProduct_mulVec_nonneg,
      ``Matrix.mulVec_diagonal, ``Finset.single_le_sum, ``mul_le_mul_iff_right₀] do
    unless dependencies.contains name do throwError "Missing material dependency {name}"
    logInfo m!"RETAINED {name}"
  if dependencies.contains reference then throwError "Reference theorem entered the proof closure"
  logInfo m!"HARMONIC_PROJECT_COUNT {seen.length}"

#assert_trust kernel NLA.RA09.outerSquare_mulVec
#assert_trust kernel NLA.RA09.diagonal_outer_quadratic
#assert_trust kernel NLA.RA09.harmonic_constraint_proved
#print axioms NLA.RA09.outerSquare_mulVec
#print axioms NLA.RA09.diagonal_outer_quadratic
#print axioms NLA.RA09.harmonic_constraint_proved
