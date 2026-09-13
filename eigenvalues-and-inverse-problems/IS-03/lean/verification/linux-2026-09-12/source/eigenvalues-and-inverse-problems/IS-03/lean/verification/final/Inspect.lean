/- Actual proof-term traversal from the complete conjecture negation. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.IS03.not_derivativeRealizabilityConjecture]
  let mut visited : List Name := []
  let mut constants : List Name := []
  for _ in [:1000] do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      if !visited.contains name then
        visited := name :: visited
        let some info := env.find? name | throwError "Missing declaration: {name}"
        if let some body := info.value? (allowOpaque := true) then
          let used := body.getUsedConstants.toList
          constants := used ++ constants
          let deps := used.filter (fun n => n.toString.startsWith "NLA.IS03." ||
            n.toString.startsWith "_private.NLA.IS03.")
          logInfo m!"PROJECT_EDGE {name}: {deps}"
          pending := deps ++ pending
  unless pending.isEmpty do throwError "Incomplete dependency traversal"
  for required in [``Matrix.pow_apply_nonneg,
      ``Matrix.charpoly_reindex, ``Matrix.charpoly_fromBlocks_zero₁₂,
      ``Matrix.det_fin_three, ``Matrix.det_succ_row_zero,
      ``Polynomial.card_rootSet_eq_natDegree,
      ``Module.End.hasEigenvalue_iff_isRoot_charpoly,
      ``Module.End.HasEigenvalue.exists_hasEigenvector,
      ``Module.End.eigenvectors_linearIndependent',
      ``basisOfLinearIndependentOfCardEqFinrank',
      ``Module.End.HasEigenvector.pow_apply,
      ``LinearMap.trace_eq_matrix_trace, ``Matrix.trace_toLin'_eq,
      ``Matrix.toLin'_pow, ``Matrix.map_pow, ``AddMonoidHom.map_trace,
      ``Matrix.charpoly_diagonal, ``LinearMap.charpoly_toMatrix,
      ``Matrix.charpoly_toLin', ``Matrix.charpoly_map,
      ``MvPolynomial.psum_eq_mul_esymm_sub_sum,
      ``Multiset.prod_X_sub_C_coeff,
      ``LeanCert.Validity.verify_strict_upper_bound_dyadic_checked,
      ``NLA.IS03.derivativePolynomial_separable,
      ``NLA.IS03.exists_root_eigenbasis,
      ``NLA.IS03.root_product_and_trace,
      ``NLA.IS03.power_sums_of_derivative_product,
      ``NLA.IS03.numerical_negative_moment,
      ``NLA.IS03.trace_moment_certificate_proved,
      ``NLA.IS03.negative_moment_proved,
      ``NLA.IS03.counterexample_proved,
      ``NLA.IS03.not_derivativeRealizabilityConjecture_proved] do
    unless constants.contains required do
      throwError "Missing retained mathematical dependency: {required}"
    logInfo m!"RETAINED_DEPENDENCY: {required}"
  for forbidden in [``sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler] do
    if constants.contains forbidden then throwError "Forbidden dependency: {forbidden}"
  logInfo m!"PROJECT_DECLARATIONS_REACHABLE_FROM_FULL_NEGATION: {visited.length}"

#check NLA.IS03.nonnegative_power_trace
#check NLA.IS03.witness_admissible
#check NLA.IS03.witness_polynomials
#check NLA.IS03.trace_moment_certificate
#check NLA.IS03.negative_moment
#check NLA.IS03.counterexample
#check NLA.IS03.not_derivativeRealizabilityConjecture

set_option pp.all true in
#print NLA.IS03.DerivativeRealizabilityConjecture
set_option pp.all true in
#print NLA.IS03.trace_moment_certificate
set_option pp.proofs true in
#print NLA.IS03.numerical_negative_moment
set_option pp.proofs true in
#print NLA.IS03.derivativePolynomial_separable
set_option pp.proofs true in
#print NLA.IS03.exists_root_eigenbasis
set_option pp.proofs true in
#print NLA.IS03.root_product_and_trace
set_option pp.proofs true in
#print NLA.IS03.trace_moment_certificate_proved
set_option pp.proofs true in
#print NLA.IS03.counterexample_proved

#assert_trust kernel NLA.IS03.derivativePolynomial_separable
#assert_trust kernel NLA.IS03.exists_root_eigenbasis
#assert_trust kernel NLA.IS03.root_product_and_trace
