/- Independent root proof-term audit. Traversal organization is reused from prior campaign reviews; requirements were checked against all actual proof modules. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.MI22.singular_values_semantics,
    ``NLA.MI22.spectral_power_semantics,
    ``NLA.MI22.euclidean_norm_bounds,
    ``NLA.MI22.witness_rational_data,
    ``NLA.MI22.witness_principal_powers,
    ``NLA.MI22.witness_operator_gap,
    ``NLA.MI22.counterexample,
    ``NLA.MI22.not_weightedLogMajorizationConjecture]
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
            n.toString.startsWith "NLA.MI22." ||
              n.toString.startsWith "_private.NLA.MI22.")
          logInfo m!"PROJECT_EDGE {name}: {projectDeps}"
          pending := projectDeps ++ pending
  unless pending.isEmpty do throwError "Dependency traversal did not finish"
  for required in [``LinearMap.singularValues_nonneg,
      ``LinearMap.singularValues_antitone,
      ``LinearMap.singularValues_of_finrank_le,
      ``LinearMap.singularValues_fin,
      ``LinearMap.sq_singularValues_of_lt,
      ``Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ``Matrix.toLpLin_mul_same,
      ``IsSelfAdjoint.norm_pow_two_pow,
      ``CFC.rpow_rpow,
      ``CFC.rpow_eq_cfc_real,
      ``Matrix.IsHermitian.cfc_eq,
      ``LeanCert.Validity.verify_strict_upper_bound_dyadic_checked,
      ``NLA.MI22.operatorNorm_posSemidef_eq_first,
      ``NLA.MI22.singularValue_zero_eq_operatorNorm,
      ``NLA.MI22.witnessT_ldl,
      ``NLA.MI22.witness_normalized_root,
      ``NLA.MI22.witness_left_mul_root,
      ``NLA.MI22.witnessRoot_norm_lt,
      ``NLA.MI22.numerical_separation,
      ``NLA.MI22.counterexample_proved,
      ``NLA.MI22.not_weightedLogMajorizationConjecture_proved] do
    unless allConstants.contains required do
      throwError "Missing actual mathematical dependency: {required}"
    logInfo m!"RETAINED_DEPENDENCY: {required}"
  logInfo m!"PROJECT_DECLARATIONS: {visited.length}"

#check NLA.MI22.singular_values_semantics
#check NLA.MI22.spectral_power_semantics
#check NLA.MI22.euclidean_norm_bounds
#check NLA.MI22.witness_rational_data
#check NLA.MI22.witness_principal_powers
#check NLA.MI22.witness_operator_gap
#check NLA.MI22.counterexample
#check NLA.MI22.not_weightedLogMajorizationConjecture

set_option pp.proofs true in
#print NLA.MI22.WeightedLogMajorizationConjecture

set_option pp.proofs true in
#print NLA.MI22.SingularLogMajorized

set_option pp.proofs true in
#print NLA.MI22.singularValue

set_option pp.proofs true in
#print NLA.MI22.operatorNorm

set_option pp.proofs true in
#print NLA.MI22.spectralPower

set_option pp.proofs true in
#print NLA.MI22.numerical_separation

set_option pp.proofs true in
#print NLA.MI22.witness_operator_gap_proved

set_option pp.proofs true in
#print NLA.MI22.counterexample_proved

set_option pp.proofs true in
#print NLA.MI22.not_weightedLogMajorizationConjecture_proved
