/- Independent proof-term inspection by final referee 1; uses the reviewer's
prior MI-23 traversal pattern, not the author's checker. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let isProject := fun n : Name => n.toString.startsWith "NLA.MI22." ||
    n.toString.startsWith "_private.NLA.MI22."
  let mut pending := [``NLA.MI22.singular_values_semantics, ``NLA.MI22.spectral_power_semantics, ``NLA.MI22.euclidean_norm_bounds, ``NLA.MI22.witness_rational_data, ``NLA.MI22.witness_principal_powers, ``NLA.MI22.witness_operator_gap, ``NLA.MI22.counterexample, ``NLA.MI22.not_weightedLogMajorizationConjecture]
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
          logInfo m!"PROJECT_EDGE {name}: {constants.filter isProject}"
          pending := constants.filter isProject ++ pending
  unless pending.isEmpty do throwError "Project traversal did not finish"
  for required in [``LinearMap.singularValues_nonneg, ``LinearMap.singularValues_antitone, ``LinearMap.singularValues_of_finrank_le, ``LinearMap.singularValues_fin, ``LinearMap.sq_singularValues_of_lt, ``Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ``Matrix.toLpLin_mul_same, ``IsSelfAdjoint.norm_pow_two_pow, ``CFC.rpow_rpow, ``CFC.rpow_eq_cfc_real, ``Matrix.IsHermitian.cfc_eq, ``Matrix.PosDef.conjTranspose_mul_mul_same, ``NLA.MI22.operatorNorm_posSemidef_eq_first, ``NLA.MI22.singularValue_zero_eq_operatorNorm, ``NLA.MI22.witnessT_ldl, ``NLA.MI22.witness_normalized_root, ``NLA.MI22.witness_left_mul_root, ``NLA.MI22.witnessRoot_norm_lt, ``NLA.MI22.witnessAB_frobeniusSquared_lt, ``NLA.MI22.witnessTestValue_gt, ``NLA.MI22.numerical_separation] do
    unless allConstants.contains required do
      throwError "Missing participating semantic dependency: {required}"
    logInfo m!"RETAINED_SEMANTIC_DEPENDENCY: {required}"
  logInfo m!"PROJECT_DECLARATIONS_TRAVERSED: {visited.length}"
  let mut current := ``NLA.MI22.not_weightedLogMajorizationConjecture
  for target in ["NLA.MI22.not_weightedLogMajorizationConjecture_proved",
      "NLA.MI22.counterexample_proved", "NLA.MI22.numerical_separation"] do
    let some info := env.find? current | throwError "Missing {current}"
    let some body := info.value? (allowOpaque := true) | throwError "Missing body {current}"
    let some next := body.getUsedConstants.find? (fun n => n.toString == target)
      | throwError "Missing direct certificate-consumer edge {current} -> {target}"
    logInfo m!"RETAINED_CERTIFICATE_EDGE: {current} -> {next}"
    current := next
  let some scalar := env.find? current | throwError "Missing scalar"
  let some body := scalar.value? (allowOpaque := true) | throwError "Missing scalar body"
  unless body.getUsedConstants.any
      (fun n => n.toString == "LeanCert.Validity.verify_strict_upper_bound_dyadic_checked") do
    throwError "Actual kernel-checked LeanCert theorem missing from scalar certificate"
  logInfo m!"ACTUAL_SCALAR_DIRECT_CONSTANTS: {body.getUsedConstants}"

set_option pp.proofs true in
#print NLA.MI22.numerical_separation
set_option pp.proofs true in
#print NLA.MI22.counterexample_proved
set_option pp.explicit true in
#print NLA.MI22.WeightedLogMajorizationConjecture
set_option pp.explicit true in
#print NLA.MI22.SingularLogMajorized
set_option pp.explicit true in
#print NLA.MI22.singularPrefix
set_option pp.explicit true in
#print NLA.MI22.singularValue
set_option pp.explicit true in
#print NLA.MI22.spectralPower
set_option pp.explicit true in
#print NLA.MI22.weightedMean
set_option pp.explicit true in
#print NLA.MI22.leftProduct
set_option pp.explicit true in
#print NLA.MI22.operatorNorm
set_option pp.explicit true in
#print NLA.MI22.frobeniusSquared
set_option pp.explicit true in
#print NLA.MI22.witnessRoot
set_option pp.explicit true in
#print NLA.MI22.witnessTestValue
#check @NLA.MI22.singular_values_semantics
#assert_trust kernel NLA.MI22.singular_values_semantics
#print axioms NLA.MI22.singular_values_semantics
#check @NLA.MI22.spectral_power_semantics
#assert_trust kernel NLA.MI22.spectral_power_semantics
#print axioms NLA.MI22.spectral_power_semantics
#check @NLA.MI22.euclidean_norm_bounds
#assert_trust kernel NLA.MI22.euclidean_norm_bounds
#print axioms NLA.MI22.euclidean_norm_bounds
#check @NLA.MI22.witness_rational_data
#assert_trust kernel NLA.MI22.witness_rational_data
#print axioms NLA.MI22.witness_rational_data
#check @NLA.MI22.witness_principal_powers
#assert_trust kernel NLA.MI22.witness_principal_powers
#print axioms NLA.MI22.witness_principal_powers
#check @NLA.MI22.witness_operator_gap
#assert_trust kernel NLA.MI22.witness_operator_gap
#print axioms NLA.MI22.witness_operator_gap
#check @NLA.MI22.counterexample
#assert_trust kernel NLA.MI22.counterexample
#print axioms NLA.MI22.counterexample
#check @NLA.MI22.not_weightedLogMajorizationConjecture
#assert_trust kernel NLA.MI22.not_weightedLogMajorizationConjecture
#print axioms NLA.MI22.not_weightedLogMajorizationConjecture
