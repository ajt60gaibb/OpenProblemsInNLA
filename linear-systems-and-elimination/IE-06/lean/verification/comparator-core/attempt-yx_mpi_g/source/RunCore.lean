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

def requireRejection (label needle : String) (result : Except String Unit) : IO Unit := do
  match result with
  | .ok _ => throw <| IO.userError s!"{label}: unexpectedly accepted"
  | .error err =>
    if (err.splitOn needle).length < 2 then
      throw <| IO.userError s!"{label}: unexpected rejection reason: {err}"
    IO.println s!"PASS {label}: {err}"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← imported `FixtureChallenge
  let matching ← imported `FixtureMatch
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  requireSuccess "matching theorem and definition" <|
    Comparator.compareAt challenge matching #[`claim] #[] #[]
  requireSuccess "matching theorem permitted axioms" <|
    Comparator.checkAxioms matching #[`claim] #[] allowed
  let mismatch ← imported `FixtureMismatch
  requireRejection "different theorem type" "theorem statement do not match" <|
    Comparator.compareAt challenge mismatch #[`claim] #[] #[]
  let changed ← imported `FixtureChangedDefinition
  requireRejection "changed meaning behind same theorem type" "Const does not match" <|
    Comparator.compareAt challenge changed #[`claim] #[] #[]
  let kindMismatch ← imported `FixtureKindMismatch
  requireRejection "theorem replaced by axiom" "constant kind don't match" <|
    Comparator.compareAt challenge kindMismatch #[`claim] #[] #[]
  let admitted ← imported `FixtureSorry
  requireSuccess "admitted theorem still has matching statement" <|
    Comparator.compareAt challenge admitted #[`claim] #[] #[]
  requireRejection "sorry proof axiom" "Illegal axiom detected: 'sorryAx'" <|
    Comparator.checkAxioms admitted #[`claim] #[] allowed
  let native ← imported `FixtureNative
  requireSuccess "native theorem still has matching statement" <|
    Comparator.compareAt challenge native #[`claim] #[] #[]
  requireRejection "native execution axiom" "Illegal axiom detected: 'claim._native.native_decide." <|
    Comparator.checkAxioms native #[`claim] #[] allowed
  IO.println "All nine Comparator-core fixture assertions passed."
