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
  | .error err => throw <| IO.userError s!"{label}: unexpected rejection: {err}"
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← imported `Challenge
  let solution ← imported `NLA.Proofs.RA05.SupportMinimum
  for name in #[`NLA.Proofs.RA05.SupportMinimum.rowCost_nonneg, `NLA.Proofs.RA05.SupportMinimum.cost_nonneg, `NLA.Proofs.RA05.SupportMinimum.strongCoreset_one, `NLA.Proofs.RA05.SupportMinimum.supportSize_one, `NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_support, `NLA.Proofs.RA05.SupportMinimum.minimumSupport_attained, `NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_rowCount, `NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_worstSupport] do
    requireSuccess s!"exact statement and referenced definitions: {name}" <| Comparator.compareAt challenge solution #[name] #[] #[]
    requireSuccess s!"transitive standard axioms: {name}" <| Comparator.checkAxioms solution #[name] #[] #[`propext, `Classical.choice, `Quot.sound]
  IO.println "All actual support statement/axiom comparisons passed."
