/- Independent final inspection; adapts the reviewer’s earlier MI-26 and RA-07 traversal patterns. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let isProject := fun n : Name => n.toString.startsWith "NLA.MI23." ||
    n.toString.startsWith "_private.NLA.MI23."
  let mut pending := [``NLA.MI23.positive_powers_and_means, ``NLA.MI23.product_eigenvalue_semantics, ``NLA.MI23.squared_product_largest, ``NLA.MI23.operator_norm_bounds, ``NLA.MI23.witness_data, ``NLA.MI23.witness_squared_gap, ``NLA.MI23.counterexample, ``NLA.MI23.not_generalizedGeometricMeanConjecture]
  let mut visited : List Name := []
  let mut allConstants : List Name := []
  for _ in [:1500] do
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
  for required in [``CFC.rpow_add, ``CFC.rpow_natCast, ``CFC.rpow_rpow,
      ``Matrix.IsHermitian.roots_charpoly_eq_eigenvalues,
      ``Matrix.IsHermitian.det_eq_prod_eigenvalues,
      ``Matrix.IsHermitian.spectral_theorem, ``Matrix.charpoly_mul_comm,
      ``Matrix.l2_opNorm_diagonal, ``Matrix.l2_opNorm_conjTranspose_mul_self,
      ``NLA.MI23.product_eigenvalue_semantics_proved,
      ``NLA.MI23.squared_product_largest_proved,
      ``NLA.MI23.entry_le_operatorNorm,
      ``NLA.MI23.trace_gram_eq_frobeniusSquared,
      ``NLA.MI23.witnessT_ldl, ``NLA.MI23.witnessT_eighth_root,
      ``NLA.MI23.witnessT_seven_eighths,
      ``NLA.MI23.witness_GH_entry, ``NLA.MI23.witness_frobenius_AB,
      ``NLA.MI23.witness_exact_gap, ``NLA.MI23.witness_strict_norm_gap,
      ``NLA.MI23.scalar_gap_positive] do
    unless allConstants.contains required do
      throwError "Missing participating semantic dependency: {required}"
    logInfo m!"RETAINED_SEMANTIC_DEPENDENCY: {required}"
  logInfo m!"PROJECT_DECLARATIONS_TRAVERSED: {visited.length}"
  let mut current := ``NLA.MI23.not_generalizedGeometricMeanConjecture
  for target in ["NLA.MI23.not_generalizedGeometricMeanConjecture_proved",
      "NLA.MI23.witness_not_logMajorized", "NLA.MI23.witness_largest_strict_gap",
      "NLA.MI23.witness_strict_norm_gap", "NLA.MI23.squaredGap_positive",
      "NLA.MI23.scalar_gap_positive"] do
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

#print NLA.MI23.scalar_gap_positive
set_option pp.explicit true in
#print NLA.MI23.GeneralizedGeometricMeanConjecture
set_option pp.explicit true in
#print NLA.MI23.spectralPower
set_option pp.explicit true in
#print NLA.MI23.generalizedMean
set_option pp.explicit true in
#print NLA.MI23.orderedEigenvalues
set_option pp.explicit true in
#print NLA.MI23.HasOrderedPositiveEigenvalues
set_option pp.explicit true in
#print NLA.MI23.LogMajorized
set_option pp.explicit true in
#print NLA.MI23.largestEigenvalue
set_option pp.explicit true in
#print NLA.MI23.operatorNorm
set_option pp.explicit true in
#print NLA.MI23.frobeniusSquared
#check @NLA.MI23.positive_powers_and_means
#assert_trust kernel NLA.MI23.positive_powers_and_means
#print axioms NLA.MI23.positive_powers_and_means
#check @NLA.MI23.product_eigenvalue_semantics
#assert_trust kernel NLA.MI23.product_eigenvalue_semantics
#print axioms NLA.MI23.product_eigenvalue_semantics
#check @NLA.MI23.squared_product_largest
#assert_trust kernel NLA.MI23.squared_product_largest
#print axioms NLA.MI23.squared_product_largest
#check @NLA.MI23.operator_norm_bounds
#assert_trust kernel NLA.MI23.operator_norm_bounds
#print axioms NLA.MI23.operator_norm_bounds
#check @NLA.MI23.witness_data
#assert_trust kernel NLA.MI23.witness_data
#print axioms NLA.MI23.witness_data
#check @NLA.MI23.witness_squared_gap
#assert_trust kernel NLA.MI23.witness_squared_gap
#print axioms NLA.MI23.witness_squared_gap
#check @NLA.MI23.counterexample
#assert_trust kernel NLA.MI23.counterexample
#print axioms NLA.MI23.counterexample
#check @NLA.MI23.not_generalizedGeometricMeanConjecture
#assert_trust kernel NLA.MI23.not_generalizedGeometricMeanConjecture
#print axioms NLA.MI23.not_generalizedGeometricMeanConjecture
