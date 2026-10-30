import NLA.Proofs.RE06.Frobenius
import NLA.Statements.RE06
import Reviewed.RE06
set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#transcript_theorem " n:ident : command => do
  let d ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? d with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected actual theorem declaration"

namespace NLA.Proofs.RE06.TranscriptAudit
 theorem live_frozen_identity : NLA.Statements.RE06.Target =
     NLA.ReviewedStatements.RE06.Target := rfl
end NLA.Proofs.RE06.TranscriptAudit

#transcript_theorem NLA.Proofs.RE06.scan_le_initial
#assert_trust kernel NLA.Proofs.RE06.scan_le_initial
#print axioms NLA.Proofs.RE06.scan_le_initial

#transcript_theorem NLA.Proofs.RE06.scan_le_member
#assert_trust kernel NLA.Proofs.RE06.scan_le_member
#print axioms NLA.Proofs.RE06.scan_le_member

#transcript_theorem NLA.Proofs.RE06.minimumIndex_score_le
#assert_trust kernel NLA.Proofs.RE06.minimumIndex_score_le
#print axioms NLA.Proofs.RE06.minimumIndex_score_le

#transcript_theorem NLA.Proofs.RE06.storedVector_finRange
#assert_trust kernel NLA.Proofs.RE06.storedVector_finRange
#print axioms NLA.Proofs.RE06.storedVector_finRange

#transcript_theorem NLA.Proofs.RE06.answer_standardBasis
#assert_trust kernel NLA.Proofs.RE06.answer_standardBasis
#print axioms NLA.Proofs.RE06.answer_standardBasis

#transcript_theorem NLA.Proofs.RE06.oracleAnswers_full
#assert_trust kernel NLA.Proofs.RE06.oracleAnswers_full
#print axioms NLA.Proofs.RE06.oracleAnswers_full

#transcript_theorem NLA.Proofs.RE06.storedVector_full
#assert_trust kernel NLA.Proofs.RE06.storedVector_full
#print axioms NLA.Proofs.RE06.storedVector_full

#transcript_theorem NLA.Proofs.RE06.postprocess_full
#assert_trust kernel NLA.Proofs.RE06.postprocess_full
#print axioms NLA.Proofs.RE06.postprocess_full

#transcript_theorem NLA.Proofs.RE06.run_full_error
#assert_trust kernel NLA.Proofs.RE06.run_full_error
#print axioms NLA.Proofs.RE06.run_full_error

#transcript_theorem NLA.Proofs.RE06.frobenius_nonnegative
#assert_trust kernel NLA.Proofs.RE06.frobenius_nonnegative
#print axioms NLA.Proofs.RE06.frobenius_nonnegative

#transcript_theorem NLA.Proofs.RE06.successful_full_branch
#assert_trust kernel NLA.Proofs.RE06.successful_full_branch
#print axioms NLA.Proofs.RE06.successful_full_branch

#transcript_theorem NLA.Proofs.RE06.storedVector_append_left
#assert_trust kernel NLA.Proofs.RE06.storedVector_append_left
#print axioms NLA.Proofs.RE06.storedVector_append_left

#transcript_theorem NLA.Proofs.RE06.storedVector_append_right
#assert_trust kernel NLA.Proofs.RE06.storedVector_append_right
#print axioms NLA.Proofs.RE06.storedVector_append_right

#transcript_theorem NLA.Proofs.RE06.oracleAnswers_sketch
#assert_trust kernel NLA.Proofs.RE06.oracleAnswers_sketch
#print axioms NLA.Proofs.RE06.oracleAnswers_sketch

#transcript_theorem NLA.Proofs.RE06.storedVector_sketch0
#assert_trust kernel NLA.Proofs.RE06.storedVector_sketch0
#print axioms NLA.Proofs.RE06.storedVector_sketch0

#transcript_theorem NLA.Proofs.RE06.storedVector_sketch1
#assert_trust kernel NLA.Proofs.RE06.storedVector_sketch1
#print axioms NLA.Proofs.RE06.storedVector_sketch1

#transcript_theorem NLA.Proofs.RE06.storedVector_sketchH
#assert_trust kernel NLA.Proofs.RE06.storedVector_sketchH
#print axioms NLA.Proofs.RE06.storedVector_sketchH

#transcript_theorem NLA.Proofs.RE06.postprocess_sketch
#assert_trust kernel NLA.Proofs.RE06.postprocess_sketch
#print axioms NLA.Proofs.RE06.postprocess_sketch

#transcript_theorem NLA.Proofs.RE06.sketchWarmIndex_score_le
#assert_trust kernel NLA.Proofs.RE06.sketchWarmIndex_score_le
#print axioms NLA.Proofs.RE06.sketchWarmIndex_score_le

#transcript_theorem NLA.Proofs.RE06.frobenius_eq_norm_sub
#assert_trust kernel NLA.Proofs.RE06.frobenius_eq_norm_sub
#print axioms NLA.Proofs.RE06.frobenius_eq_norm_sub

#transcript_theorem NLA.Proofs.RE06.frobenius_triangle
#assert_trust kernel NLA.Proofs.RE06.frobenius_triangle
#print axioms NLA.Proofs.RE06.frobenius_triangle

#transcript_theorem NLA.Proofs.RE06.frobenius_symmetric
#assert_trust kernel NLA.Proofs.RE06.frobenius_symmetric
#print axioms NLA.Proofs.RE06.frobenius_symmetric

#transcript_theorem NLA.Proofs.RE06.frobenius_minimumIndex_le
#assert_trust kernel NLA.Proofs.RE06.frobenius_minimumIndex_le
#print axioms NLA.Proofs.RE06.frobenius_minimumIndex_le

#transcript_theorem NLA.Proofs.RE06.frobenius_eq_zero_iff
#assert_trust kernel NLA.Proofs.RE06.frobenius_eq_zero_iff
#print axioms NLA.Proofs.RE06.frobenius_eq_zero_iff

#transcript_theorem NLA.Proofs.RE06.nearest_family_error
#assert_trust kernel NLA.Proofs.RE06.nearest_family_error
#print axioms NLA.Proofs.RE06.nearest_family_error

#transcript_theorem NLA.Proofs.RE06.run_sketch_error
#assert_trust kernel NLA.Proofs.RE06.run_sketch_error
#print axioms NLA.Proofs.RE06.run_sketch_error

#transcript_theorem NLA.Proofs.RE06.run_sketch_error_of_repair
#assert_trust kernel NLA.Proofs.RE06.run_sketch_error_of_repair
#print axioms NLA.Proofs.RE06.run_sketch_error_of_repair

#assert_trust kernel NLA.Proofs.RE06.TranscriptAudit.live_frozen_identity
