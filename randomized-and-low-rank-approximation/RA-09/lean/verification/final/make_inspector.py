"""Generate author term inspection: actual scopes and imports; no proof generation.
Generic traversal adapted from RA08 independent final referee2 and author checks.
"""
from pathlib import Path
import json
P=Path(__file__).resolve().parents[2]
names=json.loads((P/'comparator.json').read_text())['theorem_names']
common=['concaveFrobeniusTransferConjecture_proved','trace_deficit_reduction_proved',
 'truncation_semantics_proved','selected_cfc_eq','spectralCombination_frobenius',
 'positive_tail_transfer_proved','zero_tail_closure_proved','functionTail_of_vanishing',
 'frobeniusSquared_eq_zero','function_residual_scale_bound','restricted_auxiliary_average',
 'selected_column_average','positive_column_average','zero_column_average_proved',
 'weighted_harmonic_identity','weighted_scalar_identity','ordered_scalar_certificate_proved',
 'scalar_branch_certificates_proved','admissible_scalar_consequences_proved',
 'overlap_semantics_proved','overlap_rankOne_order','selected_rankOne_le',
 'harmonic_constraint_proved','diagonal_outer_quadratic','overlap_error_expansions_proved',
 'spectralCombination_trace_product','spectral_auxiliary_sum','spectral_tail_scaling']
extra=['orderedSpectral_exists_proved','orderedSpectral_semantics_proved',
 'functionalCalculus_spectral_proved','frobenius_semantics_proved',
 'frobeniusSquared_norm','frobenius_orthogonal_invariance_proved']
quote=lambda ns:'['+',\n      '.join('``'+n for n in ns)+']'
s='''/- Author validation of actual elaborated declaration types, bodies and dependencies.
Not an independent final review and not an implementation import. Pure exact
LeanCert kernel trust auditing is intentional; there is no numerical interval.
-/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let exports := EXPORTS
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
    let common := COMMON
    let extra := EXTRA
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
'''.replace('EXPORTS',quote(names),1).replace('COMMON',quote(['NLA.RA09.'+n for n in common])).replace('EXTRA',quote(['NLA.RA09.'+n for n in extra]))
s+='\n'+'\n'.join('#check '+n for n in names)+'\n'
for n in ['ConcaveFrobeniusTransferConjecture','OrderedSpectralData','AdmissibleFunction',
          'frobeniusNorm','frobeniusSquared','functionalCalculus','truncation','functionTruncation']:
    s+='\nset_option pp.all true in\n#print NLA.RA09.'+n+'\n'
for n in ['selected_column_average','function_residual_scale_bound',
          'positive_tail_transfer_proved','zero_tail_closure_proved','concaveFrobeniusTransferConjecture_proved']:
    s+='\nset_option pp.proofs true in\n#print NLA.RA09.'+n+'\n'
(P/'verification/final/Inspect.lean').write_text(s)
