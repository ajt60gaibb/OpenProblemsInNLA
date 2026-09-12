import Main

/-
Kernel regression cases for Comparator.runBuiltinKernel with the
Lean 4.33.1 replay API adaptation, using self-contained test declarations.
-/

open Lean

namespace PinnedReplayProbe

def context : Comparator.Context where
  projectDir := "."
  challengeModule := `UnusedChallenge
  solutionModule := `UnusedSolution
  theoremNames := #[]
  definitionNames := #[]
  legalAxioms := #[]
  leanPrefix := "."
  gitLocation := "."
  whichLandrun := "unused"
  whichLean4Export := "unused"
  externalKernels := {}

partial def collectClosure (env : Kernel.Environment) (work : List Name)
    (found : Std.HashMap Name ConstantInfo := {}) : IO (Std.HashMap Name ConstantInfo) := do
  match work with
  | [] => return found
  | name :: rest =>
    if found.contains name then
      collectClosure env rest found
    else
      let some info := env.find? name |
        throw <| IO.userError s!"Trusted fixture is missing {name}"
      collectClosure env (info.getUsedConstantsAsSet.toList ++ rest) (found.insert name info)

def exportOf (constMap : Std.HashMap Name ConstantInfo) : Export.ExportedEnv where
  constMap := constMap
  constOrder := constMap.toArray.map (·.1)

def trueProof (name : Name) : ConstantInfo := .thmInfo {
  name := name
  levelParams := []
  type := .const ``True []
  value := .const ``True.intro []
}

def invoke (label : String) (constMap : Std.HashMap Name ConstantInfo) : IO (Option String) := do
  IO.println s!"BEGIN {label}"
  let result ← ReaderT.run (Comparator.runBuiltinKernel (exportOf constMap)) context
  match result with
  | none => IO.println s!"RETURN {label}: accepted"
  | some reason => IO.println s!"RETURN {label}: rejected: {reason}"
  return result

def run : IO Unit := do
  let trusted ← Lean.importModules #[{ module := `Init }] {} (trustLevel := 0)
  -- Include constructors/recursors explicitly to exercise their post-checks.
  -- Eq must be available because replay inserts the primitive quotient family.
  let base ← collectClosure trusted.toKernelEnv
    [``True, ``True.intro, ``True.rec, ``False, ``Eq, ``Eq.refl, ``Eq.rec,
     ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
  IO.println s!"Trusted base fixture: {base.size} constants"

  let honest := base.insert `PinnedReplayProbe.honest (trueProof `PinnedReplayProbe.honest)
  if (← invoke "honest_with_inductives_and_quotients" honest).isSome then
    throw <| IO.userError "Honest fixture was rejected"

  let invalid : ConstantInfo := .thmInfo {
    name := `PinnedReplayProbe.invalid
    levelParams := []
    type := .const ``False []
    value := .const ``True.intro []
  }
  let some badReason ← invoke "invalid_raw_proof" (base.insert invalid.name invalid) |
    throw <| IO.userError "Invalid raw proof was accepted"
  unless badReason.contains "while replaying declaration 'PinnedReplayProbe.invalid'" &&
      badReason.contains "type mismatch" do
    throw <| IO.userError s!"Invalid proof failed at an unexpected phase: {badReason}"

  -- Only this exported entry is changed. Replay erases it, regenerates the
  -- genuine quotient primitive, and the actual Comparator post-check must
  -- reject the discrepancy between the exported and generated declarations.
  let fakeQuotLift := trueProof ``Quot.lift
  let some quotReason ← invoke "quotient_postcheck_mismatch"
      (base.insert ``Quot.lift fakeQuotLift) |
    throw <| IO.userError "Fake exported Quot.lift was accepted"
  unless quotReason == "Quotient constant mismatch on: Quot.lift" do
    throw <| IO.userError s!"Quotient fixture failed at an unexpected phase: {quotReason}"

  IO.println "PASS: all three actual Comparator.runBuiltinKernel cases behaved as required"

end PinnedReplayProbe

#eval PinnedReplayProbe.run
