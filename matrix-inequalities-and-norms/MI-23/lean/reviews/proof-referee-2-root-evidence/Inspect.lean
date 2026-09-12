/- Independent final review: actual retained math and kernel certificate. -/
import Solution
import Lean.Util.FoldConsts

set_option leancert.trust "kernel"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut todo := [``NLA.MI23.positive_powers_and_means,
    ``NLA.MI23.product_eigenvalue_semantics, ``NLA.MI23.squared_product_largest,
    ``NLA.MI23.operator_norm_bounds, ``NLA.MI23.witness_data,
    ``NLA.MI23.witness_squared_gap, ``NLA.MI23.counterexample,
    ``NLA.MI23.not_generalizedGeometricMeanConjecture]
  let mut seen : List Name := []
  let mut constants : List Name := []
  for _ in [:4000] do
    if let name :: rest := todo then
      todo := rest
      if !seen.contains name then
        seen := name :: seen
        let some info := env.find? name | throwError "Missing declaration: {name}"
        if let some body := info.value? (allowOpaque := true) then
          let used := body.getUsedConstants.toList
          constants := used ++ constants
          let localUsed := used.filter (fun n => n.toString.startsWith "NLA.MI23." ||
            n.toString.startsWith "_private.NLA.MI23.")
          logInfo m!"ROOT_PROOF_EDGE {name}: {localUsed}"
          todo := localUsed ++ todo
  unless todo.isEmpty do throwError "Incomplete dependency traversal"
  for required in [``LeanCert.Validity.verify_strict_upper_bound_dyadic_checked,
      ``CFC.rpow_rpow, ``Matrix.charpoly_mul_comm,
      ``Matrix.IsHermitian.roots_charpoly_eq_eigenvalues,
      ``Matrix.IsHermitian.spectral_theorem, ``Matrix.l2_opNorm_conjTranspose_mul_self,
      ``NLA.MI23.ordered_eigenvalues_posDef, ``NLA.MI23.product_eigenvalue_semantics_proved,
      ``NLA.MI23.largestEigenvalue_spec, ``NLA.MI23.squared_product_largest_proved,
      ``NLA.MI23.entry_le_operatorNorm, ``NLA.MI23.trace_gram_eq_frobeniusSquared,
      ``NLA.MI23.witnessT_ldl, ``NLA.MI23.witnessA_negative_half,
      ``NLA.MI23.witness_mean_eighth, ``NLA.MI23.witness_mean_seven_eighths,
      ``NLA.MI23.scalar_gap_positive, ``NLA.MI23.squaredGap_positive,
      ``NLA.MI23.witness_exact_gap, ``NLA.MI23.witness_strict_norm_gap,
      ``NLA.MI23.witness_largest_strict_gap, ``NLA.MI23.prefix_one_eq_largest,
      ``NLA.MI23.witness_not_logMajorized] do
    unless constants.contains required do throwError "Required dependency not retained: {required}"
    logInfo m!"ROOT_RETAINED: {required}"
  logInfo m!"ROOT_TRAVERSED: {seen.length}"

#print NLA.MI23.GeneralizedGeometricMeanConjecture
#print NLA.MI23.orderedEigenvalues
#print NLA.MI23.HasOrderedPositiveEigenvalues
#print NLA.MI23.LogMajorized
#print NLA.MI23.operatorNorm
#print NLA.MI23.frobeniusSquared
set_option pp.proofs true in
#print NLA.MI23.scalar_gap_positive
#check NLA.MI23.product_eigenvalue_semantics
#check NLA.MI23.squared_product_largest
#check NLA.MI23.operator_norm_bounds
#check NLA.MI23.counterexample
#check NLA.MI23.not_generalizedGeometricMeanConjecture
#assert_trust kernel NLA.MI23.scalar_gap_positive
#assert_trust kernel NLA.MI23.counterexample
#assert_trust kernel NLA.MI23.not_generalizedGeometricMeanConjecture
#print axioms NLA.MI23.scalar_gap_positive
#print axioms NLA.MI23.counterexample
#print axioms NLA.MI23.not_generalizedGeometricMeanConjecture
