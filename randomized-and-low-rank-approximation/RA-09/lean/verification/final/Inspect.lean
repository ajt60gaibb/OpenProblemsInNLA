/- Author validation of actual elaborated declaration types, bodies and dependencies.
Not an independent final review and not an implementation import. Pure exact
LeanCert kernel trust auditing is intentional; there is no numerical interval.
-/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
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
  let isProject := fun n : Name => n.toString.startsWith "NLA.RA09." ||
    n.toString.startsWith "_private.NLA.RA09."
  for (label, starts) in [("FINAL_TARGET", [``NLA.RA09.concaveFrobeniusTransferConjecture]),
      ("ALL_EXPORTS", exports)] do
    let mut pending := starts
    let mut seen : List Name := []
    let mut used : List Name := []
    for _ in [:8000] do
      match pending with
      | [] => pure ()
      | name :: rest =>
        pending := rest
        unless seen.contains name do
          seen := name :: seen
          let some ci := env.find? name | throwError "Missing declaration: {name}"
          if ci.isUnsafe || ci.isPartial then throwError "Unsafe/partial declaration: {name}"
          for ax in (← liftCoreM <| collectAxioms name) do
            unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
              throwError "Forbidden transitive axiom: {name}: {ax}"
          let body ← match ci.value? (allowOpaque := true) with
            | some b => pure b.getUsedConstants.toList
            | none => match ci with
              | .inductInfo _ | .ctorInfo _ | .recInfo _ => pure []
              | _ => throwError "Unexplained bodyless declaration: {name}"
          let deps := ci.type.getUsedConstants.toList ++ body
          used := deps ++ used
          let follow := deps.filter isProject
          logInfo m!"PROJECT_EDGE {label} {name}: {follow}"
          pending := follow ++ pending
    unless pending.isEmpty do throwError "Traversal incomplete: {label}"
    let common := [``NLA.RA09.concaveFrobeniusTransferConjecture_proved,
      ``NLA.RA09.trace_deficit_reduction_proved,
      ``NLA.RA09.truncation_semantics_proved,
      ``NLA.RA09.selected_cfc_eq,
      ``NLA.RA09.spectralCombination_frobenius,
      ``NLA.RA09.positive_tail_transfer_proved,
      ``NLA.RA09.zero_tail_closure_proved,
      ``NLA.RA09.functionTail_of_vanishing,
      ``NLA.RA09.frobeniusSquared_eq_zero,
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
      ``NLA.RA09.overlap_rankOne_order,
      ``NLA.RA09.selected_rankOne_le,
      ``NLA.RA09.harmonic_constraint_proved,
      ``NLA.RA09.diagonal_outer_quadratic,
      ``NLA.RA09.overlap_error_expansions_proved,
      ``NLA.RA09.spectralCombination_trace_product,
      ``NLA.RA09.spectral_auxiliary_sum,
      ``NLA.RA09.spectral_tail_scaling]
    let extra := [``NLA.RA09.orderedSpectral_exists_proved,
      ``NLA.RA09.orderedSpectral_semantics_proved,
      ``NLA.RA09.functionalCalculus_spectral_proved,
      ``NLA.RA09.frobenius_semantics_proved,
      ``NLA.RA09.frobeniusSquared_norm,
      ``NLA.RA09.frobenius_orthogonal_invariance_proved]
    let library := [``cfcHom_eq_of_continuous_of_map_id,
      ``Matrix.trace_mul_comm, ``Matrix.PosSemidef.dotProduct_mulVec_nonneg]
    let required := common ++ library ++ if label == "ALL_EXPORTS" then extra ++
      [``Matrix.IsHermitian.spectral_theorem, ``Matrix.IsHermitian.eigenvalues₀_antitone] else []
    for need in required do
      unless used.contains need do throwError "Missing material dependency {need} in {label}"
      logInfo m!"RETAINED_DEPENDENCY {label}: {need}"
    for forbidden in [``sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler] do
      if used.contains forbidden then throwError "Forbidden direct dependency: {forbidden}"
    logInfo m!"PROJECT_COUNTS {label}: declarations={seen.length}, required={required.length}"

#check NLA.RA09.frobenius_semantics
#check NLA.RA09.frobenius_orthogonal_invariance
#check NLA.RA09.orderedSpectral_exists
#check NLA.RA09.orderedSpectral_semantics
#check NLA.RA09.functionalCalculus_spectral
#check NLA.RA09.truncation_semantics
#check NLA.RA09.trace_deficit_reduction
#check NLA.RA09.admissible_scalar_consequences
#check NLA.RA09.scalar_branch_certificates
#check NLA.RA09.ordered_scalar_certificate
#check NLA.RA09.harmonic_constraint
#check NLA.RA09.overlap_semantics
#check NLA.RA09.overlap_error_expansions
#check NLA.RA09.zero_column_average
#check NLA.RA09.positive_tail_transfer
#check NLA.RA09.zero_tail_closure
#check NLA.RA09.concaveFrobeniusTransferConjecture

set_option pp.all true in
#print NLA.RA09.ConcaveFrobeniusTransferConjecture

set_option pp.all true in
#print NLA.RA09.OrderedSpectralData

set_option pp.all true in
#print NLA.RA09.AdmissibleFunction

set_option pp.all true in
#print NLA.RA09.frobeniusNorm

set_option pp.all true in
#print NLA.RA09.frobeniusSquared

set_option pp.all true in
#print NLA.RA09.functionalCalculus

set_option pp.all true in
#print NLA.RA09.truncation

set_option pp.all true in
#print NLA.RA09.functionTruncation

set_option pp.proofs true in
#print NLA.RA09.selected_column_average

set_option pp.proofs true in
#print NLA.RA09.function_residual_scale_bound

set_option pp.proofs true in
#print NLA.RA09.positive_tail_transfer_proved

set_option pp.proofs true in
#print NLA.RA09.zero_tail_closure_proved

set_option pp.proofs true in
#print NLA.RA09.concaveFrobeniusTransferConjecture_proved
