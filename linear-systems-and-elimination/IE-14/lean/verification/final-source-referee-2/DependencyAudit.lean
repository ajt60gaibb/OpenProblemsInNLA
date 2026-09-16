import Solution
import Lean.Util.FoldConsts
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for root in [``NLA.IE14.witness_data, ``NLA.IE14.witness_attainment, ``NLA.IE14.canonical_result] do
    let mut pending := [root]
    let mut seen : List Name := []
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if !seen.contains name then
        seen := name :: seen
        let some ci := env.find? name | throwError "Missing constant {name}"
        let dependencies := ci.type.getUsedConstants ++
          ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
        for child in dependencies do
          if child.toString.startsWith "NLA.IE14." then
            pending := child :: pending
    for required in [``NLA.IE14.half_complex_ne_zero, ``NLA.IE14.norm_half_complex_le_one,
                     ``NLA.IE14.half_bounds_certificate] do
      unless seen.contains required do
        throwError "Missing {required} in {root} actual compiled expression closure"
    logInfo m!"{root}: BOTH numerical helper branches and kernel certificate present in actual compiled dependency closure ({seen.length} project constants)"
#print NLA.IE14.half_complex_ne_zero
#print NLA.IE14.norm_half_complex_le_one
