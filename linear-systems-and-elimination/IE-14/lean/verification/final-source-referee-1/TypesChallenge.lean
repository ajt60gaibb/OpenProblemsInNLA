import Challenge
import Lean
open Lean Elab Command
set_option pp.all true
run_cmd do
  let env ← getEnv
  let some ci := env.find? `NLA.IE14.numerical_bounds | throwError "Missing declaration"
  logInfo m!"EXACT_TYPE NLA.IE14.numerical_bounds: {reprStr ci.type}"
  let some ci := env.find? `NLA.IE14.entryMax_semantics | throwError "Missing declaration"
  logInfo m!"EXACT_TYPE NLA.IE14.entryMax_semantics: {reprStr ci.type}"
  let some ci := env.find? `NLA.IE14.admissible_path_exists | throwError "Missing declaration"
  logInfo m!"EXACT_TYPE NLA.IE14.admissible_path_exists: {reprStr ci.type}"
  let some ci := env.find? `NLA.IE14.all_active_entries_bound | throwError "Missing declaration"
  logInfo m!"EXACT_TYPE NLA.IE14.all_active_entries_bound: {reprStr ci.type}"
  let some ci := env.find? `NLA.IE14.witness_data | throwError "Missing declaration"
  logInfo m!"EXACT_TYPE NLA.IE14.witness_data: {reprStr ci.type}"
  let some ci := env.find? `NLA.IE14.witness_attainment | throwError "Missing declaration"
  logInfo m!"EXACT_TYPE NLA.IE14.witness_attainment: {reprStr ci.type}"
  let some ci := env.find? `NLA.IE14.canonical_result | throwError "Missing declaration"
  logInfo m!"EXACT_TYPE NLA.IE14.canonical_result: {reprStr ci.type}"
