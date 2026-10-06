import Lean
import Comparator.Compare

open Lean

def imported (moduleName : Name) : IO Export.ExportedEnv := do
  let env ← importModules #[{ module := moduleName }] {} 0
  let consts := env.constants.toList
  return { constMap := Std.HashMap.ofList consts, constOrder := (consts.map Prod.fst).toArray }

def requireSuccess (label : String) (result : Except String Unit) : IO Unit := do
  match result with
  | .ok _ => IO.println s!"PASS {label}"
  | .error err => throw <| IO.userError s!"{label}: rejected: {err}"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← imported `Challenge
  let solution ← imported `Solution
  let names := #[`NLA.IE06.squareRootUpperBound, `NLA.IE06.schurSubpolynomialTail, `NLA.IE06.gaussianMatrix_probability, `NLA.IE06.exceedanceEvent_measurable, `NLA.IE06.admissiblePath_exists, `NLA.IE06.gaussianMatrix_singular_null]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    requireSuccess s!"actual theorem statement and referenced definitions: {name}" <|
      Comparator.compareAt challenge solution #[name] #[] #[]
    requireSuccess s!"actual theorem transitive proof axioms: {name}" <|
      Comparator.checkAxioms solution #[name] #[] allowed
  IO.println "All six actual IE-06 Challenge/Solution theorem comparisons and axiom checks passed."
