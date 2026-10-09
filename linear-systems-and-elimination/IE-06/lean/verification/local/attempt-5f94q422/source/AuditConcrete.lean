import Lean
import NLA.IE06.Definitions
import NLA.IE06.GEPP
import NLA.IE06.Pivot
import NLA.IE06.Reduction
import NLA.IE06.Semantics
import NLA.IE06.Statements
import KernelControl
import NLA

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let localModules : Array Name := #[`NLA.IE06.Definitions, `NLA.IE06.GEPP, `NLA.IE06.Pivot, `NLA.IE06.Reduction, `NLA.IE06.Semantics, `NLA.IE06.Statements, `KernelControl, `NLA]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[idx.toNat]? | continue
    if localModules.contains moduleName then
      let axioms ← liftCoreM <| collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "local declaration {name} uses prohibited axiom {axiomName}"
      checked := checked + 1
  logInfo m!"All {checked} concrete local declarations have permitted transitive axioms."
