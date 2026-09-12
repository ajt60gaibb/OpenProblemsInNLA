/- Independent FR-12 final referee 2 inspection.
The reviewer did not author the implementation. This file imports only Solution,
checks actual exported declarations and their consumed mathematical dependencies,
and reruns LeanCert's transitive kernel-trust audit. It is not Linux Comparator.
-/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets := [``NLA.FR12.counting_semantics, ``NLA.FR12.injective_doubling,
    ``NLA.FR12.factorial_doubling, ``NLA.FR12.power_two_nonempty,
    ``NLA.FR12.power_two_lower_bound, ``NLA.FR12.counterexample,
    ``NLA.FR12.not_countingConjecture]
  let mut pending := targets
  let mut seen : List Name := []
  let mut constants : List Name := []
  for _ in [:3000] do
    match pending with
    | [] => pure ()
    | current :: rest =>
      pending := rest
      if !seen.contains current then
        seen := current :: seen
        let some declaration := env.find? current
          | throwError "Missing actual declaration {current}"
        let some body := declaration.value? (allowOpaque := true)
          | throwError "Project declaration has no body: {current}"
        let used := body.getUsedConstants.toList
        constants := used ++ constants
        let project := used.filter (fun name =>
          name.toString.startsWith "NLA.FR12." ||
          name.toString.startsWith "_private.NLA.FR12.")
        logInfo m!"ACTUAL_EDGE {current}: {project}"
        pending := project ++ pending
  unless pending.isEmpty do throwError "Traversal did not complete"
  let required := [``Finite.of_injective, ``Matrix.IsHadamard.of_mul_conjTranspose,
    ``Nat.card_le_card_of_injective, ``Fintype.card_perm,
    ``Nat.factorial_mul_pow_sub_le_factorial, ``Real.rpow_add,
    ``Real.rpow_mul_natCast, ``Real.rpow_lt_rpow_of_exponent_lt,
    ``Real.log_pow, ``exists_nat_gt, ``NLA.FR12.finiteHadamardMatrices,
    ``NLA.FR12.isRealHadamard_iff_mathlib, ``NLA.FR12.row_inner,
    ``NLA.FR12.rows_injective, ``NLA.FR12.doubling_hadamard,
    ``NLA.FR12.doubling_injective, ``NLA.FR12.factorial_doubling_proved,
    ``NLA.FR12.count_one_pos, ``NLA.FR12.power_two_nonempty_proved,
    ``NLA.FR12.half_factorial_lower_bound, ``NLA.FR12.factorial_growth,
    ``NLA.FR12.power_two_lower_bound_proved, ``NLA.FR12.log_power_two,
    ``NLA.FR12.counterexample_proved, ``NLA.FR12.not_countingConjecture_proved]
  for name in required do
    unless constants.contains name do
      throwError "Required bridge is not consumed: {name}"
    logInfo m!"REQUIRED_CONSUMED: {name}"
  logInfo m!"REVIEWED_PROJECT_DECLARATIONS: {seen.length}"
  logInfo m!"REQUIRED_CONSUMED_COUNT: {required.length}"

#check NLA.FR12.counting_semantics
#check NLA.FR12.injective_doubling
#check NLA.FR12.factorial_doubling
#check NLA.FR12.power_two_nonempty
#check NLA.FR12.power_two_lower_bound
#check NLA.FR12.counterexample
#check NLA.FR12.not_countingConjecture

#print NLA.FR12.IsRealHadamard
#print NLA.FR12.HadamardMatrices
#print NLA.FR12.hadamardCount
set_option pp.explicit true in
#print NLA.FR12.CountingConjecture
set_option pp.explicit true in
#print NLA.FR12.doublingMatrix
#print NLA.FR12.not_countingConjecture_proved

#check Nat.card_le_card_of_injective
#check Fintype.card_perm
#check Nat.factorial_mul_pow_sub_le_factorial
#check Real.rpow_mul_natCast
#check Real.rpow_lt_rpow_of_exponent_lt
#check Real.log_pow

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
