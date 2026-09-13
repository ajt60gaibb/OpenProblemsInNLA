/- Actual MF16 proof/type traversal. Adapted from the campaign's IS03/IV06
inspector structure, with independently selected MF16 semantic dependencies.
This is an implementation-author audit, not an independent final review. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := [``NLA.MF16.word_semantics, ``NLA.MF16.source_data,
    ``NLA.MF16.twelfth_power_reduction, ``NLA.MF16.polynomial_word_equivalence,
    ``NLA.MF16.krawczyk_certificate, ``NLA.MF16.certified_root,
    ``NLA.MF16.root_to_matrix, ``NLA.MF16.counterexample,
    ``NLA.MF16.not_wordUniquenessConjecture]
  let librarySteps := [``LeanCert.Engine.krawczykCheck_sound,
    ``LeanCert.Engine.fixedPoint_iff_systemZero,
    ``LeanCert.Engine.contraction_unique_fixedPoint_in_finBox,
    ``LeanCert.Engine.newtonMap_fderiv_norm_le,
    ``LeanCert.Engine.newtonMap_mapsTo_of_imageEnclosure,
    ``LeanCert.Engine.jacobianAt_mem_intervalJacobian,
    ``LeanCert.Engine.newtonMap_differentiable,
    ``LeanCert.Engine.newtonMap_center_mem,
    ``LeanCert.Engine.systemEval_mem_pointEvalIntervals]
  let isProject := fun n : Name => n.toString.startsWith "NLA.MF16." ||
    n.toString.startsWith "_private.NLA.MF16."
  let mut pending := roots
  let mut seen : List Name := []
  let mut used : List Name := []
  for _ in [:3000] do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      unless seen.contains name do
        seen := name :: seen
        let some info := env.find? name | throwError "Missing declaration: {name}"
        if info.isUnsafe || info.isPartial then
          throwError "Unsafe or partial retained declaration: {name}"
        let axs ← liftCoreM <| collectAxioms name
        for ax in axs do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Forbidden transitive axiom at {name}: {ax}"
        let values ← match info.value? (allowOpaque := true) with
          | some body => pure body.getUsedConstants.toList
          | none => match info with
            | .inductInfo _ | .ctorInfo _ | .recInfo _ => pure []
            | _ => throwError "Bodyless project declaration: {name}"
        let constants := info.type.getUsedConstants.toList ++ values
        used := constants ++ used
        let deps := constants.filter fun n => isProject n || librarySteps.contains n
        logInfo m!"SAFE_RETAINED_EDGE {name}: {deps}"
        pending := deps ++ pending
  unless pending.isEmpty do throwError "Incomplete retained proof/type traversal"
  for required in [``NLA.MF16.actual_krawczyk_checked,
    ``NLA.MF16.certified_root_proved, ``NLA.MF16.polynomial_reduced_equivalence,
    ``NLA.MF16.polynomial_eval_zero, ``NLA.MF16.polynomial_eval_one,
    ``NLA.MF16.polynomial_eval_two, ``NLA.MF16.reducedWord_eq,
    ``NLA.MF16.matrix_twelfth_power_of_det_three,
    ``NLA.MF16.complexify_two_by_two_posDef, ``NLA.MF16.complexify_mul,
    ``NLA.MF16.complexify_pow, ``NLA.MF16.word_eq_of_two_entries,
    ``NLA.MF16.witness_word_det, ``NLA.MF16.witness_word_transpose,
    ``NLA.MF16.matrix_recovery_from_equations, ``NLA.MF16.counterexample_proved,
    ``NLA.MF16.not_wordUniquenessConjecture_proved,
    ``Matrix.aeval_self_charpoly, ``Matrix.charpoly_fin_two,
    ``Matrix.PosDef.diagonal, ``Matrix.PosDef.conjTranspose_mul_mul_same,
    ``Matrix.mulVec_injective_iff_isUnit, ``Matrix.map_pow, ``Matrix.map_mul,
    ``Matrix.det_mul, ``Matrix.det_pow, ``Matrix.det_fin_two,
    ``LeanCert.Engine.krawczykCheck_sound,
    ``LeanCert.Engine.fixedPoint_iff_systemZero,
    ``LeanCert.Engine.contraction_unique_fixedPoint_in_finBox,
    ``LeanCert.Engine.jacobianAt_mem_intervalJacobian,
    ``LeanCert.Engine.newtonMap_mapsTo_of_imageEnclosure,
    ``LeanCert.Engine.newtonMap_fderiv_norm_le,
    ``LeanCert.Engine.evalIntervalCore_correct,
    ``ContractingWith.exists_fixedPoint'] do
    unless used.contains required do throwError "Missing material dependency: {required}"
    logInfo m!"MATERIAL_DEPENDENCY: {required}"
  for forbidden in [``sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler] do
    if used.contains forbidden then throwError "Forbidden retained dependency: {forbidden}"
  logInfo m!"PROJECT_DECLARATIONS: {(seen.filter isProject).length}"
  logInfo m!"LIBRARY_SEMANTIC_PROOFS_TRAVERSED: {(seen.filter (fun n => !isProject n)).length}"

#check NLA.MF16.word_semantics
#check NLA.MF16.source_data
#check NLA.MF16.twelfth_power_reduction
#check NLA.MF16.polynomial_word_equivalence
#check NLA.MF16.krawczyk_certificate
#check NLA.MF16.certified_root
#check NLA.MF16.root_to_matrix
#check NLA.MF16.counterexample
#check NLA.MF16.not_wordUniquenessConjecture

set_option pp.all true in
#print NLA.MF16.WordUniquenessConjecture
set_option pp.all true in
#print NLA.MF16.SymmetricWord
set_option pp.all true in
#print NLA.MF16.evalWord
set_option pp.proofs true in
#print NLA.MF16.actual_krawczyk_checked
set_option pp.proofs true in
#print NLA.MF16.certified_root_proved
set_option pp.proofs true in
#print NLA.MF16.polynomial_word_equivalence_proved
set_option pp.proofs true in
#print NLA.MF16.word_eq_of_two_entries
set_option pp.proofs true in
#print NLA.MF16.root_to_matrix_proved
set_option pp.proofs true in
#print NLA.MF16.counterexample_proved
set_option pp.proofs true in
#print NLA.MF16.not_wordUniquenessConjecture_proved

#assert_trust kernel NLA.MF16.complexify_two_by_two_posDef
#assert_trust kernel NLA.MF16.word_eq_of_two_entries
#assert_trust kernel NLA.MF16.polynomial_reduced_equivalence
#assert_trust kernel LeanCert.Engine.krawczykCheck_sound
#print axioms NLA.MF16.complexify_two_by_two_posDef
#print axioms NLA.MF16.word_eq_of_two_entries
#print axioms NLA.MF16.polynomial_reduced_equivalence
#print axioms LeanCert.Engine.krawczykCheck_sound
