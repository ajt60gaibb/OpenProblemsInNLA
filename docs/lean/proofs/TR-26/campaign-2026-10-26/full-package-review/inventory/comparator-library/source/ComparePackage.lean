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
  let targets := #[`NLA.Proofs.TR26.nonisotropic_degree, `NLA.Proofs.TR26.isotropic_degree, `NLA.Proofs.TR26.target]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  requireSuccess "all three exact canonical signatures and referenced definitions" <|
    Comparator.compareAt challenge solution targets #[] #[]
  requireSuccess "all three transitive standard-only axiom closures" <|
    Comparator.checkAxioms solution targets #[] allowed
  for target in targets do
    let some (.thmInfo v) := solution.constMap[target]?
      | throw <| IO.userError "actual solution endpoint is not a theorem"
    let wrongInfo : ConstantInfo := .thmInfo { v with type := .const ``True [] }
    let wrongStatement := { solution with constMap := solution.constMap.insert target wrongInfo }
    requireReject s!"changed statement rejected: {target}" "theorem statement do not match" <|
      Comparator.compareAt challenge wrongStatement #[target] #[] #[]
    let wrongKindInfo : ConstantInfo := .axiomInfo { toConstantVal := v.toConstantVal, isUnsafe := false }
    let wrongKind := { solution with constMap := solution.constMap.insert target wrongKindInfo }
    requireReject s!"changed declaration kind rejected: {target}" "constant kind don't match" <|
      Comparator.compareAt challenge wrongKind #[target] #[] #[]
    let oracleName := `InventoryComparatorOracle
    let oracleInfo : ConstantInfo := .axiomInfo { name := oracleName, levelParams := v.levelParams, type := v.type, isUnsafe := false }
    let oracleProofInfo : ConstantInfo := .thmInfo { v with value := .const oracleName [] }
    let oracleMap := (solution.constMap.insert oracleName oracleInfo).insert target oracleProofInfo
    let oracleSolution := { solution with constMap := oracleMap }
    requireReject s!"custom exact-typed oracle proof rejected: {target}" "Illegal axiom detected" <|
      Comparator.checkAxioms oracleSolution #[target] #[] allowed
    requireReject s!"original reference hole rejected: {target}" "Illegal axiom detected" <|
      Comparator.checkAxioms challenge #[target] #[] allowed
  IO.println "PASS all fourteen actual Comparator-library signature/axiom cases"
