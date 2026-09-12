/- Independent final referee 1 inspection. No candidate declaration is changed.
The traversal is adapted from earlier campaign inspection code, but checks
both definition types and proof bodies and audits every reached project axiom.
-/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.TR15.lower_contractions, ``NLA.TR15.upper_contraction,
    ``NLA.TR15.lower_eigenvalues_pos, ``NLA.TR15.lower_eigenpair_exists,
    ``NLA.TR15.upper_negative_eigenpair, ``NLA.TR15.counterexample,
    ``NLA.TR15.not_inheritanceConjecture]
  let mut seen : List Name := []
  let mut dependencies : List Name := []
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for _ in [:2000] do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      if !seen.contains name then
        seen := name :: seen
        let some info := env.find? name | throwError "Missing declaration {name}"
        let axs ← liftCoreM <| collectAxioms name
        unless axs.all (fun ax => permitted.contains ax) do
          throwError "Forbidden transitive axiom at {name}: {axs}"
        logInfo m!"REFEREE_AXIOMS {name}: {axs}"
        let mut used := info.type.getUsedConstants.toList
        if let some value := info.value? (allowOpaque := true) then
          used := value.getUsedConstants.toList ++ used
        dependencies := used ++ dependencies
        let project := used.filter (fun n => n.toString.startsWith "NLA.TR15." ||
          n.toString.startsWith "_private.NLA.TR15.")
        logInfo m!"REFEREE_EDGE {name}: {project}"
        pending := project ++ pending
  unless pending.isEmpty do throwError "Incomplete dependency traversal"
  for expected in [``Finset.sum_eq_single, ``Finset.prod_eq_zero,
    ``Fintype.sum_equiv, ``Fintype.sum_prod_type, ``intermediate_value_Ioo,
    ``LeanCert.Validity.verify_strict_upper_bound_dyadic_checked,
    ``NLA.TR15.lower_contractions_proved, ``NLA.TR15.upper_contraction_proved,
    ``NLA.TR15.lower_eigenvalues_pos_proved, ``NLA.TR15.lower_eigenpair_exists_proved,
    ``NLA.TR15.negative_eigenvalue_certificate,
    ``NLA.TR15.upper_negative_eigenpair_proved, ``NLA.TR15.counterexample_proved,
    ``NLA.TR15.not_inheritanceConjecture_proved] do
    unless dependencies.contains expected do
      throwError "Required proof dependency absent: {expected}"
    logInfo m!"REFEREE_REQUIRED {expected}"
  logInfo m!"REFEREE_VISITED {seen.length}"

#check @NLA.TR15.lower_contractions
#check @NLA.TR15.upper_contraction
#check @NLA.TR15.lower_eigenvalues_pos
#check @NLA.TR15.lower_eigenpair_exists
#check @NLA.TR15.upper_negative_eigenpair
#check @NLA.TR15.counterexample
#check @NLA.TR15.not_inheritanceConjecture
#print NLA.TR15.Tensor
#print NLA.TR15.generatorIndex
#print NLA.TR15.hankelTensor
#print NLA.TR15.prependIndex
#print NLA.TR15.contraction
#print NLA.TR15.IsHEigenpair
#print NLA.TR15.HasNoNegativeHEigenvalues
#print NLA.TR15.lowerTensor
#print NLA.TR15.upperTensor
#print NLA.TR15.Admissible
#print NLA.TR15.InheritanceConjecture
#check @intermediate_value_Ioo

set_option pp.proofs true in
#print NLA.TR15.negative_eigenvalue_certificate
set_option pp.proofs true in
#print NLA.TR15.upper_negative_eigenpair_proved
set_option pp.proofs true in
#print NLA.TR15.counterexample_proved
set_option pp.proofs true in
#print NLA.TR15.not_inheritanceConjecture_proved
