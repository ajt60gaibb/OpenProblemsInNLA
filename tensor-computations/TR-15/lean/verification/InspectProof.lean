/- Actual declaration/dependency inspection, adapted from the campaign's
RA-07 environment traversal. This is the author's verification, not an
independent final review. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.TR15.lower_contractions, ``NLA.TR15.upper_contraction,
    ``NLA.TR15.lower_eigenvalues_pos, ``NLA.TR15.lower_eigenpair_exists,
    ``NLA.TR15.upper_negative_eigenpair, ``NLA.TR15.counterexample,
    ``NLA.TR15.not_inheritanceConjecture]
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
            n.toString.startsWith "NLA.TR15." ||
              n.toString.startsWith "_private.NLA.TR15.")
          logInfo m!"PROJECT_EDGE {name}: {projectDeps}"
          pending := projectDeps ++ pending
  unless pending.isEmpty do throwError "Dependency traversal did not finish"
  for required in [``Finset.sum_eq_single, ``Finset.prod_eq_zero,
      ``Fintype.sum_equiv, ``Fintype.sum_prod_type,
      ``intermediate_value_Ioo,
      ``LeanCert.Validity.verify_strict_upper_bound_dyadic_checked,
      ``NLA.TR15.lower_contractions_proved,
      ``NLA.TR15.upper_contraction_proved,
      ``NLA.TR15.lower_eigenvalues_pos_proved,
      ``NLA.TR15.lower_eigenpair_exists_proved,
      ``NLA.TR15.negative_eigenvalue_certificate,
      ``NLA.TR15.upper_negative_eigenpair_proved,
      ``NLA.TR15.counterexample_proved,
      ``NLA.TR15.not_inheritanceConjecture_proved] do
    unless allConstants.contains required do
      throwError "Missing actual mathematical dependency: {required}"
    logInfo m!"RETAINED_DEPENDENCY: {required}"
  logInfo m!"PROJECT_DECLARATIONS: {visited.length}"

#check NLA.TR15.lower_contractions
#check NLA.TR15.upper_contraction
#check NLA.TR15.lower_eigenvalues_pos
#check NLA.TR15.lower_eigenpair_exists
#check NLA.TR15.upper_negative_eigenpair
#check NLA.TR15.counterexample
#check NLA.TR15.not_inheritanceConjecture
