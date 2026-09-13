/- Independent root final inspection. Generic campaign FoldConsts traversal is
reused; the semantic obligations and dependencies were selected from the actual
IE23 proof. This is neither a source-text-only check nor a Comparator run. -/
import Solution
import Lean.Util.FoldConsts

set_option leancert.trust "kernel"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let exports := [``NLA.IE23.inducedNorm_semantics, ``NLA.IE23.witness_matrix_identities,
    ``NLA.IE23.fourth_power_norm_control, ``NLA.IE23.witness_action_identities,
    ``NLA.IE23.witness_attainment, ``NLA.IE23.witness_norms,
    ``NLA.IE23.witness_global_minimizers, ``NLA.IE23.not_rightInverseUniqueConjecture]
  for name in exports do
    let some (.thmInfo _) := env.find? name | throwError "Not an actual theorem: {name}"
  let mut queue := exports
  let mut visited : List Name := []
  let mut constants : List Name := []
  for _ in [:3000] do
    match queue with
    | [] => pure ()
    | name :: rest =>
      queue := rest
      if !visited.contains name then
        visited := name :: visited
        let some info := env.find? name | throwError "Missing project declaration: {name}"
        if info.isAxiom then throwError "Project axiom: {name}"
        if info.isUnsafe then throwError "Unsafe project declaration: {name}"
        let mut used := info.type.getUsedConstants.toList
        if let some body := info.value? (allowOpaque := true) then
          used := body.getUsedConstants.toList ++ used
        constants := used ++ constants
        let reached := used.filter (fun n => n.toString.startsWith "NLA.IE23." ||
          n.toString.startsWith "_private.NLA.IE23.")
        logInfo m!"CHECKED_PROJECT_EDGE {name}: {reached}"
        queue := reached ++ queue
  unless queue.isEmpty do throwError "Project dependency traversal limit exhausted"
  for required in [``EuclideanSpace.norm_sq_eq, ``Real.le_rpow_inv_iff_of_pos,
      ``Real.rpow_inv_natCast_pow, ``Real.sq_sqrt, ``Real.rpow_mul,
      ``Matrix.inv_eq_left_inv, ``Matrix.rank_mul_le_left, ``Matrix.rank_one,
      ``Matrix.rank_le_height, ``isLUB_csSup, ``le_csSup, ``csSup_le,
      ``NLA.IE23.lpNorm_pos, ``NLA.IE23.norm_coord_le_lpNorm,
      ``NLA.IE23.mulVec_lp_bound, ``NLA.IE23.ratioSet_nonempty,
      ``NLA.IE23.ratioSet_bddAbove, ``NLA.IE23.witness_gram_inverse,
      ``NLA.IE23.witness_moorePenrose, ``NLA.IE23.witness_fullRowRank,
      ``NLA.IE23.euclideanNorm_le_four_norm, ``NLA.IE23.competitor_norming_action,
      ``NLA.IE23.competitor_norm_identity, ``NLA.IE23.witnessB_inducedNorm,
      ``NLA.IE23.witnessX_inducedNorm, ``NLA.IE23.competitor_inducedNorm_lower,
      ``NLA.IE23.witness_minimum, ``NLA.IE23.full_conjecture_negation] do
    unless constants.contains required do throwError "Missing actual dependency: {required}"
    logInfo m!"REQUIRED_DEPENDENCY_PRESENT {required}"
  logInfo m!"SAFE_PROJECT_DECLARATIONS_TRAVERSED {visited.length}"
  logInfo m!"PUBLIC_THEOREM_KINDS_VERIFIED {exports.length}"

#assert_trust kernel NLA.IE23.inducedNorm_semantics
#print axioms NLA.IE23.inducedNorm_semantics
#assert_trust kernel NLA.IE23.witness_matrix_identities
#print axioms NLA.IE23.witness_matrix_identities
#assert_trust kernel NLA.IE23.fourth_power_norm_control
#print axioms NLA.IE23.fourth_power_norm_control
#assert_trust kernel NLA.IE23.witness_action_identities
#print axioms NLA.IE23.witness_action_identities
#assert_trust kernel NLA.IE23.witness_attainment
#print axioms NLA.IE23.witness_attainment
#assert_trust kernel NLA.IE23.witness_norms
#print axioms NLA.IE23.witness_norms
#assert_trust kernel NLA.IE23.witness_global_minimizers
#print axioms NLA.IE23.witness_global_minimizers
#assert_trust kernel NLA.IE23.not_rightInverseUniqueConjecture
#print axioms NLA.IE23.not_rightInverseUniqueConjecture
#assert_trust kernel NLA.IE23.ratioSet_bddAbove
#print axioms NLA.IE23.ratioSet_bddAbove
#assert_trust kernel NLA.IE23.witness_moorePenrose
#print axioms NLA.IE23.witness_moorePenrose
#assert_trust kernel NLA.IE23.competitor_inducedNorm_lower
#print axioms NLA.IE23.competitor_inducedNorm_lower
#assert_trust kernel NLA.IE23.witness_minimum
#print axioms NLA.IE23.witness_minimum

set_option pp.explicit true in
#print NLA.IE23.euclideanNorm
set_option pp.explicit true in
#print NLA.IE23.lpNorm
set_option pp.explicit true in
#print NLA.IE23.inducedNorm
set_option pp.explicit true in
#print NLA.IE23.moorePenrose
#print Matrix.rank
#print Matrix.inv
#print NLA.IE23.ratioSet
#print NLA.IE23.rightInverseNorms
#print NLA.IE23.IsNormMinimizer
#print NLA.IE23.RightInverseUniqueConjecture
#check @NLA.IE23.inducedNorm_semantics
#check @NLA.IE23.witness_matrix_identities
#check @NLA.IE23.fourth_power_norm_control
#check @NLA.IE23.witness_action_identities
#check @NLA.IE23.witness_attainment
#check @NLA.IE23.witness_norms
#check @NLA.IE23.witness_global_minimizers
#check @NLA.IE23.not_rightInverseUniqueConjecture
set_option pp.proofs true in
#print NLA.IE23.competitor_inducedNorm_lower
set_option pp.proofs true in
#print NLA.IE23.witness_minimum
set_option pp.proofs true in
#print NLA.IE23.full_conjecture_negation
