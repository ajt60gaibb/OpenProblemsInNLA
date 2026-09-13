/- Independent final referee 1: audit actual types, proof dependencies and axioms.
No candidate declaration is introduced or changed. The traversal structure is
reused from this referee's earlier campaign inspections. -/
import Solution
import Lean.Util.FoldConsts

set_option leancert.trust "kernel"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.FR12.counting_semantics, ``NLA.FR12.injective_doubling,
    ``NLA.FR12.factorial_doubling, ``NLA.FR12.power_two_nonempty,
    ``NLA.FR12.power_two_lower_bound, ``NLA.FR12.counterexample,
    ``NLA.FR12.not_countingConjecture]
  let mut seen : List Name := []
  let mut dependencies : List Name := []
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for _ in [:4096] do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      if !seen.contains name then
        seen := name :: seen
        let some info := env.find? name | throwError "Missing declaration {name}"
        let axs ← liftCoreM <| collectAxioms name
        unless axs.all (fun ax => permitted.contains ax) do
          throwError "Forbidden transitive axiom at {name}: {axs}"
        logInfo m!"REFEREE_AXIOMS {name}: {axs}"
        let mut used := info.type.getUsedConstants.toList
        if let some value := info.value? (allowOpaque := true) then
          used := value.getUsedConstants.toList ++ used
        dependencies := used ++ dependencies
        let project := used.filter (fun n => n.toString.startsWith "NLA.FR12." ||
          n.toString.startsWith "_private.NLA.FR12.")
        logInfo m!"REFEREE_EDGE {name}: {project}"
        pending := project ++ pending
  unless pending.isEmpty do throwError "Incomplete dependency traversal"
  for expected in [``Finite.of_injective, ``Matrix.IsHadamard.of_mul_conjTranspose,
    ``Nat.card_le_card_of_injective, ``Fintype.card_perm,
    ``Nat.factorial_mul_pow_sub_le_factorial, ``Real.rpow_add,
    ``Real.rpow_mul_natCast, ``Real.rpow_lt_rpow_of_exponent_lt,
    ``Real.log_pow, ``exists_nat_gt,
    ``NLA.FR12.rows_injective, ``NLA.FR12.doubling_hadamard,
    ``NLA.FR12.doubling_injective, ``NLA.FR12.factorial_doubling_proved,
    ``NLA.FR12.power_two_nonempty_proved, ``NLA.FR12.half_factorial_lower_bound,
    ``NLA.FR12.factorial_growth, ``NLA.FR12.power_two_lower_bound_proved,
    ``NLA.FR12.counterexample_proved, ``NLA.FR12.not_countingConjecture_proved] do
    unless dependencies.contains expected do
      throwError "Required actual mathematical dependency absent: {expected}"
    logInfo m!"REFEREE_REQUIRED {expected}"
  logInfo m!"REFEREE_VISITED {seen.length}"

#check @NLA.FR12.counting_semantics
#check @NLA.FR12.injective_doubling
#check @NLA.FR12.factorial_doubling
#check @NLA.FR12.power_two_nonempty
#check @NLA.FR12.power_two_lower_bound
#check @NLA.FR12.counterexample
#check @NLA.FR12.not_countingConjecture

set_option pp.explicit true in
#print NLA.FR12.IsRealHadamard
set_option pp.explicit true in
#print NLA.FR12.HadamardMatrices
set_option pp.explicit true in
#print NLA.FR12.hadamardCount
set_option pp.explicit true in
#print NLA.FR12.CountingConjecture
set_option pp.explicit true in
#print NLA.FR12.doublingMatrix
set_option pp.explicit true in
#print NLA.FR12.power_two_lower_bound

#check @Finite.of_injective
#check @Nat.card_le_card_of_injective
#check @Nat.card_pos
#check @Matrix.IsHadamard.of_mul_conjTranspose
#check @Nat.factorial_mul_pow_sub_le_factorial
#check @Real.rpow_natCast_mul
#check @Real.rpow_lt_rpow_of_exponent_lt
#check @Real.log_pow
#check @exists_nat_gt

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

set_option pp.proofs true in
#print NLA.FR12.factorial_doubling_proved
set_option pp.proofs true in
#print NLA.FR12.power_two_lower_bound_proved
set_option pp.proofs true in
#print NLA.FR12.not_countingConjecture_proved
