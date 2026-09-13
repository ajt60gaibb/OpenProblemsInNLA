/- Independent IV06 final referee 1. Traverse actual fresh final proof bodies.
The general driver design is adapted from this reviewer's MI03 and IE23
audits, with independent IV06 semantic and boundary checks. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.IV06.not_componentBoundConjecture]
  let mut seen : List Name := []
  let mut used : List Name := []
  for _ in [:2000] do
    match pending with
    | [] => pure ()
    | declaration :: rest =>
      pending := rest
      unless seen.contains declaration do
        seen := declaration :: seen
        let some info := env.find? declaration
          | throwError "Missing actual declaration: {declaration}"
        let some value := info.value? (allowOpaque := true)
          | throwError "Project declaration has no body: {declaration}"
        let dependencies := value.getUsedConstants.toList
        used := dependencies ++ used
        let localDependencies := dependencies.filter fun n =>
          n.toString.startsWith "NLA.IV06." || n.toString.startsWith "_private.NLA.IV06."
        logInfo m!"REFEREE_EDGE {declaration}: {localDependencies}"
        pending := localDependencies ++ pending
  unless pending.isEmpty do throwError "Actual proof traversal did not terminate"
  for required in [``Matrix.exists_mulVec_eq_zero_iff, ``Matrix.det_fin_three,
      ``ConnectedComponents.coe_eq_coe', ``isPreconnected_connectedComponent,
      ``IsPreconnected.image, ``IsPreconnected.Icc_subset,
      ``Cardinal.mk_le_of_injective, ``Cardinal.mk_fintype, ``Fintype.card_fin,
      ``LeanCert.Validity.verify_strict_upper_bound_dyadic_checked,
      ``NLA.IV06.numerical_separator_margin,
      ``NLA.IV06.eigenvalue_determinant_semantics_proved,
      ``NLA.IV06.interval_family_iff, ``NLA.IV06.family_characteristicDet,
      ``NLA.IV06.witness_eigenpairs_proved, ``NLA.IV06.witness_separators_proved,
      ``NLA.IV06.connected_component_intervals_proved,
      ``NLA.IV06.four_components_proved, ``NLA.IV06.counterexample_proved,
      ``NLA.IV06.not_componentBoundConjecture_proved,
      ``continuous_subtype_val, ``mem_connectedComponent,
      ``NLA.IV06.ordered_pair_separator] do
    unless used.contains required do throwError "Required dependency absent: {required}"
    logInfo m!"REFEREE_RETAINED: {required}"
  logInfo m!"REFEREE_PROJECT_DECLARATIONS: {seen.length}"

#check NLA.IV06.eigenvalue_determinant_semantics
#check NLA.IV06.family_and_determinant_semantics
#check NLA.IV06.witness_eigenpairs
#check NLA.IV06.witness_separators
#check NLA.IV06.connected_component_intervals
#check NLA.IV06.four_components
#check NLA.IV06.counterexample
#check NLA.IV06.not_componentBoundConjecture

set_option pp.all true in
#print NLA.IV06.ComponentBoundConjecture
set_option pp.all true in
#print NLA.IV06.componentCard
set_option pp.all true in
#print NLA.IV06.realEigenvalueSet
#print NLA.IV06.HasRealEigenvalue
#print Real.pseudoMetricSpace
#print ConnectedComponents
#print connectedComponent

set_option pp.proofs true in
#print NLA.IV06.numerical_separator_margin
set_option pp.proofs true in
#print NLA.IV06.eigenvalue_determinant_semantics_proved
set_option pp.proofs true in
#print NLA.IV06.witness_separators_proved
set_option pp.proofs true in
#print NLA.IV06.connected_component_intervals_proved
set_option pp.proofs true in
#print NLA.IV06.four_components_proved
set_option pp.proofs true in
#print NLA.IV06.not_componentBoundConjecture_proved

-- Independently exercise the generic bridge's zero-dimensional boundary.
example (A : NLA.IV06.RealMatrix 0) (lam : ℝ) :
    ¬ NLA.IV06.HasRealEigenvalue A lam := by
  rintro ⟨v, hv, _⟩
  exact hv (Subsingleton.elim _ _)

example (A : NLA.IV06.RealMatrix 0) (lam : ℝ) :
    NLA.IV06.characteristicDet A lam = 1 := by
  simp [NLA.IV06.characteristicDet]
