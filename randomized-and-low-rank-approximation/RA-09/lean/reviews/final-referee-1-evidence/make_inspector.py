from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parents[2]; E=Path(__file__).resolve().parent
names=json.loads((P/'comparator.json').read_text())['theorem_names']
common=['concaveFrobeniusTransferConjecture_proved','trace_deficit_reduction_proved','trace_mul_posSemidef_nonneg','frobeniusSquared_sub_identity','frobeniusSquared_eq_zero','truncation_semantics_proved','selected_cfc_eq','selectedCfcAux_continuous','selectedCfcAux_id','spectralCombination_frobenius','positive_tail_transfer_proved','zero_tail_closure_proved','functionTail_of_vanishing','function_error_of_vanishing_tail','function_residual_scale_bound','restricted_auxiliary_average','selected_column_average','positive_column_average','zero_column_average_proved','weighted_harmonic_identity','weighted_scalar_identity','ordered_scalar_certificate_proved','scalar_branch_certificates_proved','admissible_scalar_consequences_proved','overlap_semantics_proved','overlap_column_sum','overlap_row_sum','overlap_rankOne_order','selected_rankOne_le','harmonic_constraint_proved','diagonal_outer_quadratic','overlap_error_expansions_proved','spectralCombination_trace_product','spectral_auxiliary_sum','spectral_tail_scaling','cutoff_square_comparisons']
extra=['orderedSpectral_exists_proved','orderedSpectral_semantics_proved','functionalCalculus_spectral_proved','frobenius_semantics_proved','frobeniusSquared_norm','frobenius_orthogonal_invariance_proved']
library=['cfcHom_eq_of_continuous_of_map_id','Matrix.trace_mul_comm','Matrix.PosSemidef.dotProduct_mulVec_nonneg','CStarAlgebra.nonneg_iff_eq_star_mul_self']
quote=lambda ss: '['+',\n    '.join('``'+s for s in ss)+']'
text='''/- Independent final mathematical review 1. Not imported by implementation.
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
  let pairs := '''+quote([])+'''
'''
# Use explicit Name pairs to compare actual elaborated types.
text=text.replace('  let pairs := []\n','  let pairs : List (Name × Name) := [\n'+',\n'.join('    (``'+n+', ``NLA.RA09.FinalReferee1Reference.'+n.split('.')[-1]+')' for n in names)+']\n')
text+='''  for (realName, refName) in pairs do
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
  let exports := '''+quote(names)+'''
  let common := '''+quote(['NLA.RA09.'+s for s in common]+library)+'''
  let extra := '''+quote(['NLA.RA09.'+s for s in extra]+['Matrix.IsHermitian.spectral_theorem','Matrix.IsHermitian.eigenvalues₀_antitone','Matrix.frobenius_norm_def'])+'''
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
'''
for n in names: text+='\n#assert_trust kernel '+n+'\n#print axioms '+n+'\n'
for n in ['ConcaveFrobeniusTransferConjecture','AdmissibleFunction','OrderedSpectralData','frobeniusSquared','frobeniusNorm','functionalCalculus','truncation','functionTruncation','overlapWeights']:
    text+='\nset_option pp.all true in\n#print NLA.RA09.'+n+'\n'
(E/'Inspect.lean').write_text(text)
(E/'inspection-requirements.json').write_text(json.dumps({'exports':names,'common_material_bridges':['NLA.RA09.'+s for s in common]+library,'additional_all_export_bridges':['NLA.RA09.'+s for s in extra]+['Matrix.IsHermitian.spectral_theorem','Matrix.IsHermitian.eigenvalues₀_antitone','Matrix.frobenius_norm_def'],'required_type_comparisons':17,'implementation_reference_edges_allowed':0,'max_project_traversal_steps':10000,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},indent=2)+'\n')
