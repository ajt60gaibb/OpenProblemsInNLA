/- Author actual dependency audit; not an independent final review or Linux run. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.FR12.counting_semantics, ``NLA.FR12.injective_doubling, ``NLA.FR12.factorial_doubling, ``NLA.FR12.power_two_nonempty, ``NLA.FR12.power_two_lower_bound, ``NLA.FR12.counterexample, ``NLA.FR12.not_countingConjecture]
  let mut visited : List Name := []
  let mut allConstants : List Name := []
  for _ in [:2000] do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      if !visited.contains name then
        visited := name :: visited
        let some info := env.find? name | throwError "Missing declaration: {name}"
        if let some body := info.value? (allowOpaque := true) then
          let constants := body.getUsedConstants.toList
          allConstants := constants ++ allConstants
          let projectDeps := constants.filter (fun n =>
            n.toString.startsWith "NLA.FR12." ||
              n.toString.startsWith "_private.NLA.FR12.")
          logInfo m!"PROJECT_EDGE {name}: {projectDeps}"
          pending := projectDeps ++ pending
  unless pending.isEmpty do throwError "Dependency traversal did not finish"
  for required in [``Finite.of_injective,
      ``Matrix.IsHadamard.of_mul_conjTranspose,
      ``Nat.card_le_card_of_injective,
      ``Fintype.card_perm,
      ``Nat.factorial_mul_pow_sub_le_factorial,
      ``Real.rpow_add,
      ``Real.rpow_mul_natCast,
      ``Real.rpow_lt_rpow_of_exponent_lt,
      ``Real.log_pow,
      ``exists_nat_gt,
      ``NLA.FR12.rows_injective,
      ``NLA.FR12.doubling_hadamard,
      ``NLA.FR12.doubling_injective,
      ``NLA.FR12.factorial_doubling_proved,
      ``NLA.FR12.power_two_nonempty_proved,
      ``NLA.FR12.half_factorial_lower_bound,
      ``NLA.FR12.factorial_growth,
      ``NLA.FR12.power_two_lower_bound_proved,
      ``NLA.FR12.counterexample_proved,
      ``NLA.FR12.not_countingConjecture_proved] do
    unless allConstants.contains required do
      throwError "Missing actual mathematical dependency: {required}"
    logInfo m!"RETAINED_DEPENDENCY: {required}"
  logInfo m!"PROJECT_DECLARATIONS: {visited.length}"


#check NLA.FR12.counting_semantics
#check NLA.FR12.injective_doubling
#check NLA.FR12.factorial_doubling
#check NLA.FR12.power_two_nonempty
#check NLA.FR12.power_two_lower_bound
#check NLA.FR12.counterexample
#check NLA.FR12.not_countingConjecture

set_option pp.explicit true in
#print NLA.FR12.CountingConjecture
set_option pp.explicit true in
#print NLA.FR12.doublingMatrix

#assert_trust kernel NLA.FR12.counting_semantics
#print axioms NLA.FR12.counting_semantics
#assert_trust kernel NLA.FR12.injective_doubling
#print axioms NLA.FR12.injective_doubling
#assert_trust kernel NLA.FR12.factorial_doubling
#print axioms NLA.FR12.factorial_doubling
#assert_trust kernel NLA.FR12.power_two_nonempty
#print axioms NLA.FR12.power_two_nonempty
#assert_trust kernel NLA.FR12.power_two_lower_bound
#print axioms NLA.FR12.power_two_lower_bound
#assert_trust kernel NLA.FR12.counterexample
#print axioms NLA.FR12.counterexample
#assert_trust kernel NLA.FR12.not_countingConjecture
#print axioms NLA.FR12.not_countingConjecture
