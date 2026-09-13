/- Actual IE23 dependency and semantic inspection. The traversal structure is
adapted from this author's independent MI03 referee inspection and earlier
campaign audits. This is an author check, not an independent referee report. -/
import Solution
import Lean.Util.FoldConsts

set_option leancert.trust "kernel"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.IE23.inducedNorm_semantics,
    ``NLA.IE23.witness_matrix_identities, ``NLA.IE23.fourth_power_norm_control,
    ``NLA.IE23.witness_action_identities, ``NLA.IE23.witness_attainment,
    ``NLA.IE23.witness_norms, ``NLA.IE23.witness_global_minimizers,
    ``NLA.IE23.not_rightInverseUniqueConjecture]
  let mut seen : List Name := []
  let mut used : List Name := []
  for _ in [:2000] do
    match pending with
    | [] => pure ()
    | declaration :: rest =>
      pending := rest
      unless seen.contains declaration do
        seen := declaration :: seen
        let some info := env.find? declaration
          | throwError "Missing actual declaration: {declaration}"
        let some value := info.value? (allowOpaque := true)
          | throwError "Project declaration has no actual body: {declaration}"
        let dependencies := value.getUsedConstants.toList
        used := dependencies ++ used
        let localDependencies := dependencies.filter fun n =>
          n.toString.startsWith "NLA.IE23." || n.toString.startsWith "_private.NLA.IE23."
        logInfo m!"ACTUAL_EDGE {declaration}: {localDependencies}"
        pending := localDependencies ++ pending
  unless pending.isEmpty do throwError "Actual proof traversal did not terminate"
  for required in [``EuclideanSpace.norm_sq_eq, ``Real.rpow_pos_of_pos,
      ``Real.le_rpow_inv_iff_of_pos, ``Finset.sum_sq_le_sq_sum_of_nonneg,
      ``Matrix.rank_mul_le_left, ``Matrix.rank_one, ``Matrix.rank_le_height,
      ``Matrix.inv_eq_left_inv, ``Real.rpow_inv_natCast_pow,
      ``Real.sqrt_eq_rpow, ``Real.sq_sqrt, ``le_csSup, ``csSup_le, ``isLUB_csSup,
      ``NLA.IE23.norm_coord_le_lpNorm, ``NLA.IE23.mulVec_lp_bound,
      ``NLA.IE23.ratioSet_bddAbove, ``NLA.IE23.ratioSet_nonempty,
      ``NLA.IE23.ratio_le_inducedNorm, ``NLA.IE23.inducedNorm_le_of_bound,
      ``NLA.IE23.witness_gram_inverse, ``NLA.IE23.witness_moorePenrose,
      ``NLA.IE23.witness_fullRowRank, ``NLA.IE23.lpNorm_fourth_power,
      ``NLA.IE23.euclideanNorm_le_four_norm, ``NLA.IE23.witnessB_norm_identity,
      ``NLA.IE23.competitor_norming_action, ``NLA.IE23.competitor_norm_identity,
      ``NLA.IE23.normingVector_lpNorm, ``NLA.IE23.witnessB_norming_ratio,
      ``NLA.IE23.witnessX_norming_ratio, ``NLA.IE23.witnessB_inducedNorm,
      ``NLA.IE23.witnessX_inducedNorm, ``NLA.IE23.competitor_inducedNorm_lower,
      ``NLA.IE23.witnessB_global_minimizer, ``NLA.IE23.witnessX_global_minimizer,
      ``NLA.IE23.witness_minimum, ``NLA.IE23.full_conjecture_negation] do
    unless used.contains required do throwError "Required dependency absent: {required}"
    logInfo m!"ACTUAL_RETAINED: {required}"
  logInfo m!"ACTUAL_PROJECT_DECLARATIONS: {seen.length}"

#check NLA.IE23.inducedNorm_semantics
#check NLA.IE23.witness_matrix_identities
#check NLA.IE23.fourth_power_norm_control
#check NLA.IE23.witness_action_identities
#check NLA.IE23.witness_attainment
#check NLA.IE23.witness_norms
#check NLA.IE23.witness_global_minimizers
#check NLA.IE23.not_rightInverseUniqueConjecture

set_option pp.explicit true in
#print NLA.IE23.euclideanNorm
set_option pp.explicit true in
#print NLA.IE23.lpNorm
#print NLA.IE23.ratioSet
#print NLA.IE23.inducedNorm
#print NLA.IE23.FullRowRank
#print NLA.IE23.moorePenrose
#print NLA.IE23.RightInverseUniqueConjecture
#print NLA.IE23.IsNormMinimizer
#print NLA.IE23.rightInverseNorms

set_option pp.proofs true in
#print NLA.IE23.norm_coord_le_lpNorm
set_option pp.proofs true in
#print NLA.IE23.ratioSet_bddAbove
set_option pp.proofs true in
#print NLA.IE23.inducedNorm_semantics_proved
set_option pp.proofs true in
#print NLA.IE23.witness_gram_inverse
set_option pp.proofs true in
#print NLA.IE23.witness_fullRowRank
set_option pp.proofs true in
#print NLA.IE23.euclideanNorm_le_four_norm
set_option pp.proofs true in
#print NLA.IE23.competitor_norming_action
set_option pp.proofs true in
#print NLA.IE23.competitor_inducedNorm_lower
set_option pp.proofs true in
#print NLA.IE23.witness_minimum
set_option pp.proofs true in
#print NLA.IE23.full_conjecture_negation
