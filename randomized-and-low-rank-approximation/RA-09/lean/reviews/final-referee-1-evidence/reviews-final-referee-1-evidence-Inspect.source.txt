/- Independent final mathematical review 1. Not imported by implementation.
The derived reference changes only its namespace; its 17 admitted bodies are
used solely to elaborate frozen types. Actual implementation closures are
separately audited and must not reach that namespace. This local comparison
is not the authoritative sandboxed Ubuntu Comparator.
-/
import Solution
import reviews.«final-referee-1-evidence».Reference
import Lean.Util.FoldConsts

set_option maxHeartbeats 1200000
set_option leancert.trust "kernel"
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pairs : List (Name × Name) := [
    (``NLA.RA09.frobenius_semantics, ``NLA.RA09.FinalReferee1Reference.frobenius_semantics),
    (``NLA.RA09.frobenius_orthogonal_invariance, ``NLA.RA09.FinalReferee1Reference.frobenius_orthogonal_invariance),
    (``NLA.RA09.orderedSpectral_exists, ``NLA.RA09.FinalReferee1Reference.orderedSpectral_exists),
    (``NLA.RA09.orderedSpectral_semantics, ``NLA.RA09.FinalReferee1Reference.orderedSpectral_semantics),
    (``NLA.RA09.functionalCalculus_spectral, ``NLA.RA09.FinalReferee1Reference.functionalCalculus_spectral),
    (``NLA.RA09.truncation_semantics, ``NLA.RA09.FinalReferee1Reference.truncation_semantics),
    (``NLA.RA09.trace_deficit_reduction, ``NLA.RA09.FinalReferee1Reference.trace_deficit_reduction),
    (``NLA.RA09.admissible_scalar_consequences, ``NLA.RA09.FinalReferee1Reference.admissible_scalar_consequences),
    (``NLA.RA09.scalar_branch_certificates, ``NLA.RA09.FinalReferee1Reference.scalar_branch_certificates),
    (``NLA.RA09.ordered_scalar_certificate, ``NLA.RA09.FinalReferee1Reference.ordered_scalar_certificate),
    (``NLA.RA09.harmonic_constraint, ``NLA.RA09.FinalReferee1Reference.harmonic_constraint),
    (``NLA.RA09.overlap_semantics, ``NLA.RA09.FinalReferee1Reference.overlap_semantics),
    (``NLA.RA09.overlap_error_expansions, ``NLA.RA09.FinalReferee1Reference.overlap_error_expansions),
    (``NLA.RA09.zero_column_average, ``NLA.RA09.FinalReferee1Reference.zero_column_average),
    (``NLA.RA09.positive_tail_transfer, ``NLA.RA09.FinalReferee1Reference.positive_tail_transfer),
    (``NLA.RA09.zero_tail_closure, ``NLA.RA09.FinalReferee1Reference.zero_tail_closure),
    (``NLA.RA09.concaveFrobeniusTransferConjecture, ``NLA.RA09.FinalReferee1Reference.concaveFrobeniusTransferConjecture)]
  for (realName, refName) in pairs do
    let some realInfo := env.find? realName | throwError "Missing implementation {realName}"
    let some refInfo := env.find? refName | throwError "Missing frozen reference {refName}"
    match realInfo with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected an actual theorem {realName}"
    liftTermElabM do
      unless ← Lean.Meta.isDefEq realInfo.type refInfo.type do
        throwError "Elaborated signature differs: {realName}"
    let refAxioms ← liftCoreM <| collectAxioms refName
    unless refAxioms.contains ``sorryAx do
      throwError "Reference diagnostic did not retain deliberate admission: {refName}"
    logInfo m!"EXACT_ELABORATED_SIGNATURE {realName} = {refName}"
    logInfo m!"EXPORTED_TYPE {realName}: {realInfo.type}"
  let exports := [``NLA.RA09.frobenius_semantics,
    ``NLA.RA09.frobenius_orthogonal_invariance,
    ``NLA.RA09.orderedSpectral_exists,
    ``NLA.RA09.orderedSpectral_semantics,
    ``NLA.RA09.functionalCalculus_spectral,
    ``NLA.RA09.truncation_semantics,
    ``NLA.RA09.trace_deficit_reduction,
    ``NLA.RA09.admissible_scalar_consequences,
    ``NLA.RA09.scalar_branch_certificates,
    ``NLA.RA09.ordered_scalar_certificate,
    ``NLA.RA09.harmonic_constraint,
    ``NLA.RA09.overlap_semantics,
    ``NLA.RA09.overlap_error_expansions,
    ``NLA.RA09.zero_column_average,
    ``NLA.RA09.positive_tail_transfer,
    ``NLA.RA09.zero_tail_closure,
    ``NLA.RA09.concaveFrobeniusTransferConjecture]
  let common := [``NLA.RA09.concaveFrobeniusTransferConjecture_proved,
    ``NLA.RA09.trace_deficit_reduction_proved,
    ``NLA.RA09.trace_mul_posSemidef_nonneg,
    ``NLA.RA09.frobeniusSquared_sub_identity,
    ``NLA.RA09.frobeniusSquared_eq_zero,
    ``NLA.RA09.truncation_semantics_proved,
    ``NLA.RA09.selected_cfc_eq,
    ``NLA.RA09.selectedCfcAux_continuous,
    ``NLA.RA09.selectedCfcAux_id,
    ``NLA.RA09.spectralCombination_frobenius,
    ``NLA.RA09.positive_tail_transfer_proved,
    ``NLA.RA09.zero_tail_closure_proved,
    ``NLA.RA09.functionTail_of_vanishing,
    ``NLA.RA09.function_error_of_vanishing_tail,
    ``NLA.RA09.function_residual_scale_bound,
    ``NLA.RA09.restricted_auxiliary_average,
    ``NLA.RA09.selected_column_average,
    ``NLA.RA09.positive_column_average,
    ``NLA.RA09.zero_column_average_proved,
    ``NLA.RA09.weighted_harmonic_identity,
    ``NLA.RA09.weighted_scalar_identity,
    ``NLA.RA09.ordered_scalar_certificate_proved,
    ``NLA.RA09.scalar_branch_certificates_proved,
    ``NLA.RA09.admissible_scalar_consequences_proved,
    ``NLA.RA09.overlap_semantics_proved,
    ``NLA.RA09.overlap_column_sum,
    ``NLA.RA09.overlap_row_sum,
    ``NLA.RA09.overlap_rankOne_order,
    ``NLA.RA09.selected_rankOne_le,
    ``NLA.RA09.harmonic_constraint_proved,
    ``NLA.RA09.diagonal_outer_quadratic,
    ``NLA.RA09.overlap_error_expansions_proved,
    ``NLA.RA09.spectralCombination_trace_product,
    ``NLA.RA09.spectral_auxiliary_sum,
    ``NLA.RA09.spectral_tail_scaling,
    ``NLA.RA09.cutoff_square_comparisons,
    ``cfcHom_eq_of_continuous_of_map_id,
    ``Matrix.trace_mul_comm,
    ``Matrix.PosSemidef.dotProduct_mulVec_nonneg,
    ``CStarAlgebra.nonneg_iff_eq_star_mul_self]
  let extra := [``NLA.RA09.orderedSpectral_exists_proved,
    ``NLA.RA09.orderedSpectral_semantics_proved,
    ``NLA.RA09.functionalCalculus_spectral_proved,
    ``NLA.RA09.frobenius_semantics_proved,
    ``NLA.RA09.frobeniusSquared_norm,
    ``NLA.RA09.frobenius_orthogonal_invariance_proved,
    ``Matrix.IsHermitian.spectral_theorem,
    ``Matrix.IsHermitian.eigenvalues₀_antitone,
    ``Matrix.frobenius_norm_def]
  let isProject := fun n : Name => n.toString.startsWith "NLA.RA09." ||
    n.toString.startsWith "_private.NLA.RA09."
  for (label, starts) in [("FINAL", [``NLA.RA09.concaveFrobeniusTransferConjecture]),
      ("ALL", exports)] do
    let mut todo := starts
    let mut seen : List Name := []
    let mut allDeps : List Name := []
    for _ in [:10000] do
      match todo with
      | [] => pure ()
      | name :: rest =>
        todo := rest
        unless seen.contains name do
          if name.toString.startsWith "NLA.RA09.FinalReferee1Reference." then
            throwError "Real proof reached admitted reference {name}"
          seen := name :: seen
          let some ci := env.find? name | throwError "Missing dependency {name}"
          if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial dependency {name}"
          let axs ← liftCoreM <| collectAxioms name
          for ax in axs do
            unless [``propext, ``Quot.sound, ``Classical.choice].contains ax do
              throwError "Forbidden actual transitive axiom {name}: {ax}"
          let valueDeps ← match ci.value? (allowOpaque := true) with
            | some body => pure body.getUsedConstants.toList
            | none => match ci with
              | .inductInfo _ | .ctorInfo _ | .recInfo _ => pure []
              | _ => throwError "Unexplained bodyless project declaration {name}"
          let ds := ci.type.getUsedConstants.toList ++ valueDeps
          allDeps := ds ++ allDeps
          let following := ds.filter isProject
          todo := following ++ todo
          logInfo m!"ACTUAL_EDGE {label} {name}: {following}"
          logInfo m!"ACTUAL_AXIOMS {label} {name}: {axs.toList}"
    unless todo.isEmpty do throwError "Incomplete traversal {label}"
    let must := common ++ if label == "ALL" then extra else []
    for need in must do
      unless allDeps.contains need do throwError "Required bridge absent in {label}: {need}"
      logInfo m!"MATERIAL_BRIDGE {label}: {need}"
    logInfo m!"INDEPENDENT_COUNTS {label}: project={seen.length}, material={must.length}"

#assert_trust kernel NLA.RA09.frobenius_semantics
#print axioms NLA.RA09.frobenius_semantics

#assert_trust kernel NLA.RA09.frobenius_orthogonal_invariance
#print axioms NLA.RA09.frobenius_orthogonal_invariance

#assert_trust kernel NLA.RA09.orderedSpectral_exists
#print axioms NLA.RA09.orderedSpectral_exists

#assert_trust kernel NLA.RA09.orderedSpectral_semantics
#print axioms NLA.RA09.orderedSpectral_semantics

#assert_trust kernel NLA.RA09.functionalCalculus_spectral
#print axioms NLA.RA09.functionalCalculus_spectral

#assert_trust kernel NLA.RA09.truncation_semantics
#print axioms NLA.RA09.truncation_semantics

#assert_trust kernel NLA.RA09.trace_deficit_reduction
#print axioms NLA.RA09.trace_deficit_reduction

#assert_trust kernel NLA.RA09.admissible_scalar_consequences
#print axioms NLA.RA09.admissible_scalar_consequences

#assert_trust kernel NLA.RA09.scalar_branch_certificates
#print axioms NLA.RA09.scalar_branch_certificates

#assert_trust kernel NLA.RA09.ordered_scalar_certificate
#print axioms NLA.RA09.ordered_scalar_certificate

#assert_trust kernel NLA.RA09.harmonic_constraint
#print axioms NLA.RA09.harmonic_constraint

#assert_trust kernel NLA.RA09.overlap_semantics
#print axioms NLA.RA09.overlap_semantics

#assert_trust kernel NLA.RA09.overlap_error_expansions
#print axioms NLA.RA09.overlap_error_expansions

#assert_trust kernel NLA.RA09.zero_column_average
#print axioms NLA.RA09.zero_column_average

#assert_trust kernel NLA.RA09.positive_tail_transfer
#print axioms NLA.RA09.positive_tail_transfer

#assert_trust kernel NLA.RA09.zero_tail_closure
#print axioms NLA.RA09.zero_tail_closure

#assert_trust kernel NLA.RA09.concaveFrobeniusTransferConjecture
#print axioms NLA.RA09.concaveFrobeniusTransferConjecture

set_option pp.all true in
#print NLA.RA09.ConcaveFrobeniusTransferConjecture

set_option pp.all true in
#print NLA.RA09.AdmissibleFunction

set_option pp.all true in
#print NLA.RA09.OrderedSpectralData

set_option pp.all true in
#print NLA.RA09.frobeniusSquared

set_option pp.all true in
#print NLA.RA09.frobeniusNorm

set_option pp.all true in
#print NLA.RA09.functionalCalculus

set_option pp.all true in
#print NLA.RA09.truncation

set_option pp.all true in
#print NLA.RA09.functionTruncation

set_option pp.all true in
#print NLA.RA09.overlapWeights
