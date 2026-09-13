/- Independent IS-03 final referee 2 inspection.
Adapted from this reviewer's earlier generic type/body FoldConsts traversal.
All seven public closures are roots; mathematical requirements are selected
from the actual IS-03 implementation and pinned primary APIs. -/
import Solution
import Lean.Util.FoldConsts

set_option leancert.trust "kernel"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let exports := [``NLA.IS03.nonnegative_power_trace, ``NLA.IS03.witness_admissible,
    ``NLA.IS03.witness_polynomials, ``NLA.IS03.trace_moment_certificate,
    ``NLA.IS03.negative_moment, ``NLA.IS03.counterexample,
    ``NLA.IS03.not_derivativeRealizabilityConjecture]
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
        let reached := used.filter (fun n => n.toString.startsWith "NLA.IS03." ||
          n.toString.startsWith "_private.NLA.IS03.")
        logInfo m!"CHECKED_PROJECT_EDGE {name}: {reached}"
        queue := reached ++ queue
  unless queue.isEmpty do throwError "Project dependency traversal limit exhausted"
  for required in [``Polynomial.separable_def', ``Polynomial.card_rootSet_eq_natDegree,
      ``Module.End.hasEigenvalue_iff_isRoot_charpoly,
      ``Module.End.HasEigenvalue.exists_hasEigenvector,
      ``Module.End.eigenvectors_linearIndependent',
      ``basisOfLinearIndependentOfCardEqFinrank',
      ``Module.End.HasEigenvector.pow_apply,
      ``Matrix.charpoly_toLin', ``Matrix.charpoly_map, ``Matrix.charpoly_diagonal,
      ``LinearMap.charpoly_toMatrix, ``Matrix.toLin'_pow,
      ``Matrix.map_pow, ``AddMonoidHom.map_trace,
      ``Matrix.trace_toLin'_eq, ``LinearMap.trace_eq_matrix_trace,
      ``Matrix.pow_apply_nonneg, ``Matrix.charpoly_reindex,
      ``Matrix.charpoly_fromBlocks_zero₁₂, ``Matrix.det_fin_three,
      ``Matrix.det_succ_row_zero, ``Multiset.prod_X_sub_C_coeff,
      ``MvPolynomial.aeval_esymm_eq_multiset_esymm,
      ``MvPolynomial.psum_eq_mul_esymm_sub_sum,
      ``Complex.ofReal_injective,
      ``LeanCert.Validity.verify_strict_upper_bound_dyadic_checked,
      ``NLA.IS03.derivativePolynomial_separable, ``NLA.IS03.complexRoots_card,
      ``NLA.IS03.exists_root_eigenbasis, ``NLA.IS03.root_product_and_trace,
      ``NLA.IS03.product_coeff_eq_elementary, ``NLA.IS03.powerMoments_newton,
      ``NLA.IS03.power_sums_of_derivative_product,
      ``NLA.IS03.witness_charpoly, ``NLA.IS03.witness_normalizedDerivative,
      ``NLA.IS03.numerical_negative_moment, ``NLA.IS03.negative_moment_proved,
      ``NLA.IS03.trace_moment_certificate_proved, ``NLA.IS03.counterexample_proved,
      ``NLA.IS03.not_derivativeRealizabilityConjecture_proved] do
    unless constants.contains required do throwError "Missing actual dependency: {required}"
    logInfo m!"REQUIRED_DEPENDENCY_PRESENT {required}"
  for forbidden in [``sorryAx, `Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler] do
    if constants.contains forbidden then throwError "Forbidden dependency: {forbidden}"
  logInfo m!"SAFE_PROJECT_DECLARATIONS_TRAVERSED {visited.length}"
  logInfo m!"PUBLIC_THEOREM_KINDS_VERIFIED {exports.length}"

#assert_trust kernel NLA.IS03.nonnegative_power_trace
#print axioms NLA.IS03.nonnegative_power_trace
#assert_trust kernel NLA.IS03.witness_admissible
#print axioms NLA.IS03.witness_admissible
#assert_trust kernel NLA.IS03.witness_polynomials
#print axioms NLA.IS03.witness_polynomials
#assert_trust kernel NLA.IS03.trace_moment_certificate
#print axioms NLA.IS03.trace_moment_certificate
#assert_trust kernel NLA.IS03.negative_moment
#print axioms NLA.IS03.negative_moment
#assert_trust kernel NLA.IS03.counterexample
#print axioms NLA.IS03.counterexample
#assert_trust kernel NLA.IS03.not_derivativeRealizabilityConjecture
#print axioms NLA.IS03.not_derivativeRealizabilityConjecture
#assert_trust kernel NLA.IS03.derivativePolynomial_separable
#print axioms NLA.IS03.derivativePolynomial_separable
#assert_trust kernel NLA.IS03.exists_root_eigenbasis
#print axioms NLA.IS03.exists_root_eigenbasis
#assert_trust kernel NLA.IS03.root_product_and_trace
#print axioms NLA.IS03.root_product_and_trace
#assert_trust kernel NLA.IS03.power_sums_of_derivative_product
#print axioms NLA.IS03.power_sums_of_derivative_product
#assert_trust kernel NLA.IS03.numerical_negative_moment
#print axioms NLA.IS03.numerical_negative_moment

#check @NLA.IS03.exists_root_eigenbasis
#check @NLA.IS03.root_product_and_trace
#check @NLA.IS03.power_sums_of_derivative_product
#check @NLA.IS03.trace_moment_certificate
#check @Polynomial.card_rootSet_eq_natDegree
#check @Module.End.eigenvectors_linearIndependent'
#check @basisOfLinearIndependentOfCardEqFinrank'
#check @Module.End.HasEigenvector.pow_apply
#check @Matrix.toLin'_pow
#check @Matrix.map_pow
#check @LinearMap.trace_eq_matrix_trace
#check @Multiset.prod_X_sub_C_coeff

set_option pp.all true in
#print NLA.IS03.DerivativeRealizabilityConjecture
set_option pp.all true in
#print NLA.IS03.trace_moment_certificate
#print NLA.IS03.ComplexRoots
#print NLA.IS03.elementaryMoments
#print NLA.IS03.powerMoments
set_option pp.proofs true in
#print NLA.IS03.derivativePolynomial_separable
set_option pp.proofs true in
#print NLA.IS03.exists_root_eigenbasis
set_option pp.proofs true in
#print NLA.IS03.root_product_and_trace
set_option pp.proofs true in
#print NLA.IS03.numerical_negative_moment
set_option pp.proofs true in
#print NLA.IS03.trace_moment_certificate_proved
set_option pp.proofs true in
#print NLA.IS03.counterexample_proved
set_option pp.proofs true in
#print NLA.IS03.not_derivativeRealizabilityConjecture_proved

set_option pp.proofs true in
#print NLA.IS03.numerical_negative_moment._proof_1_7
#assert_trust kernel NLA.IS03.numerical_negative_moment._proof_1_7
#print axioms NLA.IS03.numerical_negative_moment._proof_1_7
