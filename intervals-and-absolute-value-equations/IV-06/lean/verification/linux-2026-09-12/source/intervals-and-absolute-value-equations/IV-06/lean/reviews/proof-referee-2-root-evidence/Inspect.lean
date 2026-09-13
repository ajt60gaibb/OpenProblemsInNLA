/- Independent root final inspection. Generic campaign FoldConsts traversal is
reused; the semantic obligations and dependencies were selected from the actual
IV06 proof. This is neither a source-text-only check nor a Comparator run. -/
import Solution
import Lean.Util.FoldConsts

set_option leancert.trust "kernel"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let exports := [``NLA.IV06.eigenvalue_determinant_semantics, ``NLA.IV06.family_and_determinant_semantics, ``NLA.IV06.witness_eigenpairs, ``NLA.IV06.witness_separators, ``NLA.IV06.connected_component_intervals, ``NLA.IV06.four_components, ``NLA.IV06.counterexample, ``NLA.IV06.not_componentBoundConjecture]
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
        let reached := used.filter (fun n => n.toString.startsWith "NLA.IV06." ||
          n.toString.startsWith "_private.NLA.IV06.")
        logInfo m!"CHECKED_PROJECT_EDGE {name}: {reached}"
        queue := reached ++ queue
  unless queue.isEmpty do throwError "Project dependency traversal limit exhausted"
  for required in [``Matrix.exists_mulVec_eq_zero_iff, ``ConnectedComponents.coe_eq_coe', ``isPreconnected_connectedComponent, ``IsPreconnected.image, ``continuous_subtype_val, ``IsPreconnected.Icc_subset, ``Cardinal.mk_le_of_injective, ``Cardinal.mk_fintype, ``Fintype.card_fin, ``LeanCert.Validity.verify_strict_upper_bound_dyadic_checked, ``NLA.IV06.interval_family_iff, ``NLA.IV06.family_characteristicDet, ``NLA.IV06.witness_eigenpairs_proved, ``NLA.IV06.numerical_separator_margin, ``NLA.IV06.witness_separators_proved, ``NLA.IV06.connected_component_intervals_proved, ``NLA.IV06.ordered_pair_separator, ``NLA.IV06.four_components_proved, ``NLA.IV06.counterexample_proved, ``NLA.IV06.not_componentBoundConjecture_proved] do
    unless constants.contains required do throwError "Missing actual dependency: {required}"
    logInfo m!"REQUIRED_DEPENDENCY_PRESENT {required}"
  logInfo m!"SAFE_PROJECT_DECLARATIONS_TRAVERSED {visited.length}"
  logInfo m!"PUBLIC_THEOREM_KINDS_VERIFIED {exports.length}"

#assert_trust kernel NLA.IV06.eigenvalue_determinant_semantics
#print axioms NLA.IV06.eigenvalue_determinant_semantics
#assert_trust kernel NLA.IV06.family_and_determinant_semantics
#print axioms NLA.IV06.family_and_determinant_semantics
#assert_trust kernel NLA.IV06.witness_eigenpairs
#print axioms NLA.IV06.witness_eigenpairs
#assert_trust kernel NLA.IV06.witness_separators
#print axioms NLA.IV06.witness_separators
#assert_trust kernel NLA.IV06.connected_component_intervals
#print axioms NLA.IV06.connected_component_intervals
#assert_trust kernel NLA.IV06.four_components
#print axioms NLA.IV06.four_components
#assert_trust kernel NLA.IV06.counterexample
#print axioms NLA.IV06.counterexample
#assert_trust kernel NLA.IV06.not_componentBoundConjecture
#print axioms NLA.IV06.not_componentBoundConjecture
#assert_trust kernel NLA.IV06.numerical_separator_margin
#print axioms NLA.IV06.numerical_separator_margin
#assert_trust kernel NLA.IV06.connected_component_intervals_proved
#print axioms NLA.IV06.connected_component_intervals_proved
#assert_trust kernel NLA.IV06.four_components_proved
#print axioms NLA.IV06.four_components_proved
set_option pp.explicit true in
#print NLA.IV06.HasRealEigenvalue
set_option pp.explicit true in
#print NLA.IV06.characteristicDet
set_option pp.explicit true in
#print NLA.IV06.realEigenvalueSet
set_option pp.explicit true in
#print NLA.IV06.componentCard
set_option pp.explicit true in
#print NLA.IV06.ComponentBoundConjecture
#print ConnectedComponents
#print Real.dist_eq
#check @Matrix.exists_mulVec_eq_zero_iff
#check @IsPreconnected.Icc_subset
#check @Cardinal.mk_le_of_injective
#check @NLA.IV06.eigenvalue_determinant_semantics
#check @NLA.IV06.family_and_determinant_semantics
#check @NLA.IV06.witness_eigenpairs
#check @NLA.IV06.witness_separators
#check @NLA.IV06.connected_component_intervals
#check @NLA.IV06.four_components
#check @NLA.IV06.counterexample
#check @NLA.IV06.not_componentBoundConjecture
set_option pp.proofs true in
#print NLA.IV06.numerical_separator_margin
set_option pp.proofs true in
#print NLA.IV06.connected_component_intervals_proved
set_option pp.proofs true in
#print NLA.IV06.four_components_proved
set_option pp.proofs true in
#print NLA.IV06.not_componentBoundConjecture_proved

example (A : NLA.IV06.RealMatrix 0) (lam : ℝ) : ¬ NLA.IV06.HasRealEigenvalue A lam := by
  rintro ⟨v, hv, _⟩
  exact hv (Subsingleton.elim _ _)

example (A : NLA.IV06.RealMatrix 0) (lam : ℝ) : NLA.IV06.characteristicDet A lam = 1 := by
  simp [NLA.IV06.characteristicDet]
