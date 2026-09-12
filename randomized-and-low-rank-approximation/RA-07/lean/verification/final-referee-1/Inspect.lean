/- Independent final referee 1: actual declaration semantics and dependency use.
Reviewer: Codex agent /root/leancert_examples, not the RA-07 implementer.
The traversal pattern is adapted from the author's separately retained
verification/InspectProof.lean; all checks here are independently rerun. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.RA07.elementary_values,
    ``NLA.RA07.generating_derivative_values,
    ``NLA.RA07.positive_derivative_factorization,
    ``NLA.RA07.power_sum_certificate,
    ``NLA.RA07.second_difference_certificate,
    ``NLA.RA07.errorSequence_convex]
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
          let projectDeps := constants.filter (fun n => n.toString.startsWith "NLA.RA07.")
          logInfo m!"REFEREE_PROJECT_EDGE {name}: {projectDeps}"
          pending := projectDeps ++ pending
  unless pending.isEmpty do throwError "Dependency traversal did not finish"
  for required in [``Polynomial.rootSet_derivative_subset_convexHull_rootSet,
      ``Polynomial.Splits.of_splits_map, ``Polynomial.Splits.eq_prod_roots,
      ``Polynomial.Splits.natDegree_eq_card_roots, ``Polynomial.Splits.roots_map,
      ``Polynomial.natDegree_derivative, ``Polynomial.coeff_iterate_derivative,
      ``Finset.prod_one_add, ``Polynomial.iterate_derivative_C_mul,
      ``NLA.RA07.generating_coeff,
      ``NLA.RA07.generating_derivative_eval_pos,
      ``NLA.RA07.iterated_complex_roots_negative,
      ``NLA.RA07.real_factorization_of_negative_complex_roots,
      ``NLA.RA07.sum_square_difference_pair, ``NLA.RA07.pair_gap_identity,
      ``NLA.RA07.finite_product_derivatives, ``NLA.RA07.error_as_derivative_ratio,
      ``NLA.RA07.shifted_error_ratio] do
    unless allConstants.contains required do
      throwError "Missing actual mathematical dependency: {required}"
    logInfo m!"REFEREE_RETAINED_DEPENDENCY: {required}"
  logInfo m!"REFEREE_PROJECT_DECLARATIONS: {visited.length}"

set_option pp.explicit true in
#print NLA.RA07.elementarySymmetric
set_option pp.explicit true in
#print NLA.RA07.errorSequence
set_option pp.explicit true in
#print NLA.RA07.generatingPolynomial
set_option pp.explicit true in
#print NLA.RA07.iteratedGeneratingDerivative
set_option pp.explicit true in
#print NLA.RA07.pairGap
set_option pp.explicit true in
#print NLA.RA07.ConvexityConjecture

#check NLA.RA07.elementary_values
#check NLA.RA07.generating_derivative_values
#check NLA.RA07.positive_derivative_factorization
#check NLA.RA07.power_sum_certificate
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
