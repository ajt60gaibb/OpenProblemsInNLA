/- Independent final referee 1: actual compiled statement/term inspection.
No implementation or Challenge object is imported into this proof environment. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.IE23.inducedNorm_semantics,
    ``NLA.IE23.witness_matrix_identities, ``NLA.IE23.fourth_power_norm_control,
    ``NLA.IE23.witness_action_identities, ``NLA.IE23.witness_attainment,
    ``NLA.IE23.witness_norms, ``NLA.IE23.witness_global_minimizers,
    ``NLA.IE23.not_rightInverseUniqueConjecture]
  let mut visited : List Name := []
  let mut used : List Name := []
  for _ in [:1500] do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      if !visited.contains name then
        visited := name :: visited
        let some info := env.find? name | throwError "Missing declaration {name}"
        let some body := info.value? (allowOpaque := true) | throwError "No body for project declaration {name}"
        let constants := body.getUsedConstants.toList
        used := constants ++ used
        let localDeps := constants.filter (fun n =>
          n.toString.startsWith "NLA.IE23." || n.toString.startsWith "_private.NLA.IE23.")
        logInfo m!"MATERIAL_EDGE {name}: {localDeps}"
        pending := localDeps ++ pending
  unless pending.isEmpty do throwError "Traversal incomplete"
  for required in [``EuclideanSpace.norm_sq_eq, ``Real.rpow_pos_of_pos,
    ``Real.le_rpow_inv_iff_of_pos, ``Real.rpow_inv_natCast_pow,
    ``Real.rpow_mul, ``Real.sqrt_eq_rpow,
    ``isLUB_csSup, ``le_csSup, ``csSup_le,
    ``Matrix.inv_eq_left_inv, ``Matrix.rank_le_height,
    ``Matrix.rank_mul_le_left, ``Matrix.rank_one,
    ``NLA.IE23.lpNorm_pos, ``NLA.IE23.norm_coord_le_lpNorm,
    ``NLA.IE23.mulVec_lp_bound, ``NLA.IE23.ratioSet_nonempty,
    ``NLA.IE23.ratioSet_bddAbove, ``NLA.IE23.ratio_le_inducedNorm,
    ``NLA.IE23.inducedNorm_le_of_bound, ``NLA.IE23.witness_fullRowRank,
    ``NLA.IE23.witness_gram_isUnit, ``NLA.IE23.witness_gram_inverse,
    ``NLA.IE23.witness_moorePenrose, ``NLA.IE23.witness_B_rightInverse,
    ``NLA.IE23.witness_X_rightInverse, ``NLA.IE23.witness_B_ne_X,
    ``NLA.IE23.lpNorm_fourth_power, ``NLA.IE23.euclideanNorm_le_four_norm,
    ``NLA.IE23.witnessNorm_rpow, ``NLA.IE23.witnessB_norm_identity,
    ``NLA.IE23.witnessX_norm_identity, ``NLA.IE23.competitor_norming_action,
    ``NLA.IE23.competitor_norm_identity, ``NLA.IE23.normingVector_lpNorm,
    ``NLA.IE23.witnessB_inducedNorm, ``NLA.IE23.witnessX_inducedNorm,
    ``NLA.IE23.competitor_inducedNorm_lower, ``NLA.IE23.witness_minimum,
    ``NLA.IE23.full_conjecture_negation] do
    unless used.contains required do throwError "Missing actual dependency {required}"
    logInfo m!"RETAINED_DEPENDENCY {required}"
  for forbidden in [``sorryAx, `Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler] do
    if used.contains forbidden then throwError "Forbidden material dependency {forbidden}"
  logInfo m!"REACHABLE_PROJECT_DECLARATIONS {visited.length}"

#check NLA.IE23.inducedNorm_semantics
#check NLA.IE23.witness_matrix_identities
#check NLA.IE23.fourth_power_norm_control
#check NLA.IE23.witness_action_identities
#check NLA.IE23.witness_attainment
#check NLA.IE23.witness_norms
#check NLA.IE23.witness_global_minimizers
#check NLA.IE23.not_rightInverseUniqueConjecture

set_option pp.all true in
#print NLA.IE23.euclideanNorm
set_option pp.all true in
#print NLA.IE23.lpNorm
set_option pp.all true in
#print NLA.IE23.inducedNorm
set_option pp.all true in
#print NLA.IE23.FullRowRank
set_option pp.all true in
#print NLA.IE23.moorePenrose
set_option pp.all true in
#print NLA.IE23.IsNormMinimizer
set_option pp.all true in
#print NLA.IE23.RightInverseUniqueConjecture
set_option pp.proofs true in
#print NLA.IE23.inducedNorm_semantics_proved
set_option pp.proofs true in
#print NLA.IE23.witness_gram_inverse
set_option pp.proofs true in
#print NLA.IE23.witness_fullRowRank
set_option pp.proofs true in
#print NLA.IE23.competitor_inducedNorm_lower
set_option pp.proofs true in
#print NLA.IE23.witness_minimum
set_option pp.proofs true in
#print NLA.IE23.full_conjecture_negation
