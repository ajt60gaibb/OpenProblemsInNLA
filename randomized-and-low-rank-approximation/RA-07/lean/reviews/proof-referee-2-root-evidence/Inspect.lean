/- Independent coordinating-agent inspection; not authored by the proof agent. -/
import Solution
import Lean.Util.FoldConsts

set_option leancert.trust "kernel"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut todo := [``NLA.RA07.elementary_values,
    ``NLA.RA07.generating_derivative_values,
    ``NLA.RA07.positive_derivative_factorization,
    ``NLA.RA07.power_sum_certificate,
    ``NLA.RA07.second_difference_certificate,
    ``NLA.RA07.errorSequence_convex]
  let mut seen : List Name := []
  let mut constants : List Name := []
  for _ in [:2000] do
    if let name :: rest := todo then
      todo := rest
      if !seen.contains name then
        seen := name :: seen
        let some info := env.find? name | throwError "Declaration absent: {name}"
        if let some value := info.value? (allowOpaque := true) then
          let used := value.getUsedConstants.toList
          constants := used ++ constants
          let localUsed := used.filter (fun n => n.toString.startsWith "NLA.RA07.")
          logInfo m!"ROOT_DEPENDENCY_EDGE {name}: {localUsed}"
          todo := localUsed ++ todo
  unless todo.isEmpty do throwError "Unfinished traversal"
  for required in [``Polynomial.rootSet_derivative_subset_convexHull_rootSet,
      ``Polynomial.Splits.of_splits_map, ``Polynomial.Splits.eq_prod_roots,
      ``Polynomial.Splits.natDegree_eq_card_roots, ``Polynomial.natDegree_derivative,
      ``Polynomial.coeff_iterate_derivative, ``NLA.RA07.generating_coeff,
      ``NLA.RA07.sum_strict_upper_half, ``NLA.RA07.sum_square_difference_pair,
      ``NLA.RA07.pair_gap_identity, ``NLA.RA07.finite_product_derivatives,
      ``NLA.RA07.error_as_derivative_ratio, ``NLA.RA07.shifted_error_ratio,
      ``NLA.RA07.initial_second_difference] do
    unless constants.contains required do throwError "Dependency omitted: {required}"
    logInfo m!"ROOT_RETAINED: {required}"
  logInfo m!"ROOT_PROJECT_DECLARATION_COUNT: {seen.length}"

set_option pp.explicit true in
#print NLA.RA07.ConvexityConjecture
set_option pp.explicit true in
#print NLA.RA07.elementarySymmetric
set_option pp.explicit true in
#print NLA.RA07.errorSequence
set_option pp.explicit true in
#print NLA.RA07.iteratedGeneratingDerivative
set_option pp.explicit true in
#print NLA.RA07.pairGap
set_option pp.explicit true in
#print NLA.RA07.certificateDenominator
#check NLA.RA07.positive_derivative_factorization
#check NLA.RA07.second_difference_certificate
#check NLA.RA07.errorSequence_convex

#assert_trust kernel NLA.RA07.elementary_values
#assert_trust kernel NLA.RA07.generating_derivative_values
#assert_trust kernel NLA.RA07.positive_derivative_factorization
#assert_trust kernel NLA.RA07.power_sum_certificate
#assert_trust kernel NLA.RA07.second_difference_certificate
#assert_trust kernel NLA.RA07.errorSequence_convex
#print axioms NLA.RA07.elementary_values
#print axioms NLA.RA07.generating_derivative_values
#print axioms NLA.RA07.positive_derivative_factorization
#print axioms NLA.RA07.power_sum_certificate
#print axioms NLA.RA07.second_difference_certificate
#print axioms NLA.RA07.errorSequence_convex
