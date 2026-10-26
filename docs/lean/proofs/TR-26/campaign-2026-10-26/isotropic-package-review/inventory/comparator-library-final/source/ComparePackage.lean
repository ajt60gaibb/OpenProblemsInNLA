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
def requireReject (label expected : String) (result : Except String Unit) : IO Unit := do
  match result with
  | .ok _ => throw <| IO.userError s!"{label}: invalid comparison accepted"
  | .error err =>
    unless (err.splitOn expected).length > 1 do
      throw <| IO.userError s!"{label}: wrong rejection: {err}"
    IO.println s!"PASS {label}: {err}"
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← imported `Challenge
  let solution ← imported `Solution
  let target := `NLA.Proofs.TR26.isotropic_degree
  requireSuccess "exact canonical signature and referenced definitions" <|
    Comparator.compareAt challenge solution #[target] #[] #[]
  requireSuccess "transitive standard-only axioms" <|
    Comparator.checkAxioms solution #[target] #[] #[`propext, `Classical.choice, `Quot.sound]
  let some (.thmInfo v) := solution.constMap[target]?
    | throw <| IO.userError "actual solution endpoint is not a theorem"
  let wrongStatement := { solution with constMap := solution.constMap.insert target
    (.thmInfo { v with type := .const ``True [] }) }
  requireReject "changed statement rejected" "theorem statement do not match" <|
    Comparator.compareAt challenge wrongStatement #[target] #[] #[]
  let wrongKind := { solution with constMap := solution.constMap.insert target
    (.axiomInfo { toConstantVal := v.toConstantVal, isUnsafe := false }) }
  requireReject "changed declaration kind rejected" "constant kind don't match" <|
    Comparator.compareAt challenge wrongKind #[target] #[] #[]
  requireReject "unpermitted foundational axiom rejected" "Illegal axiom detected" <|
    Comparator.checkAxioms solution #[target] #[] #[]
  IO.println "PASS all five actual Comparator-library signature/axiom cases"
