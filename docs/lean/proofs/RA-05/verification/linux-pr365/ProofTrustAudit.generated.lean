import Solution
import LeanCert.Tactic.Verification
set_option autoImplicit false
set_option leancert.trust "kernel"

open Lean Elab Command in
elab "#assert_proof_constant " n:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? decl with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected a proved theorem constant"

#assert_proof_constant NLA.Proofs.RA05.SupportMinimum.rowCost_nonneg
#assert_trust kernel NLA.Proofs.RA05.SupportMinimum.rowCost_nonneg
#print axioms NLA.Proofs.RA05.SupportMinimum.rowCost_nonneg
#assert_proof_constant NLA.Proofs.RA05.SupportMinimum.cost_nonneg
#assert_trust kernel NLA.Proofs.RA05.SupportMinimum.cost_nonneg
#print axioms NLA.Proofs.RA05.SupportMinimum.cost_nonneg
#assert_proof_constant NLA.Proofs.RA05.SupportMinimum.strongCoreset_one
#assert_trust kernel NLA.Proofs.RA05.SupportMinimum.strongCoreset_one
#print axioms NLA.Proofs.RA05.SupportMinimum.strongCoreset_one
#assert_proof_constant NLA.Proofs.RA05.SupportMinimum.supportSize_one
#assert_trust kernel NLA.Proofs.RA05.SupportMinimum.supportSize_one
#print axioms NLA.Proofs.RA05.SupportMinimum.supportSize_one
#assert_proof_constant NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_support
#assert_trust kernel NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_support
#print axioms NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_support
#assert_proof_constant NLA.Proofs.RA05.SupportMinimum.minimumSupport_attained
#assert_trust kernel NLA.Proofs.RA05.SupportMinimum.minimumSupport_attained
#print axioms NLA.Proofs.RA05.SupportMinimum.minimumSupport_attained
#assert_proof_constant NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_rowCount
#assert_trust kernel NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_rowCount
#print axioms NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_rowCount
#assert_proof_constant NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_worstSupport
#assert_trust kernel NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_worstSupport
#print axioms NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_worstSupport
#assert_proof_constant NLA.Proofs.RA05.unitHyperplane_projector
#assert_trust kernel NLA.Proofs.RA05.unitHyperplane_projector
#print axioms NLA.Proofs.RA05.unitHyperplane_projector
#assert_proof_constant NLA.Proofs.RA05.rowCost_unitHyperplane
#assert_trust kernel NLA.Proofs.RA05.rowCost_unitHyperplane
#print axioms NLA.Proofs.RA05.rowCost_unitHyperplane
#assert_proof_constant NLA.Proofs.RA05.strongCoreset_implies_allVectorEmbedding
#assert_trust kernel NLA.Proofs.RA05.strongCoreset_implies_allVectorEmbedding
#print axioms NLA.Proofs.RA05.strongCoreset_implies_allVectorEmbedding
