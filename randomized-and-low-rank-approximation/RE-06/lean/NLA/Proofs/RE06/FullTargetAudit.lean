import NLA.Proofs.RE06.MainTarget
import Reviewed.RE06
set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#re06_theorem " n:ident : command => do
  let d ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? d with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected actual theorem declaration"
namespace NLA.Proofs.RE06.FullTargetAudit

theorem live_reviewed_identity : NLA.Statements.RE06.Target =
    NLA.ReviewedStatements.RE06.Target := rfl

theorem consume_svd_total  :
    NLA.Computation.NonadaptiveMatrixQuery.SVDTotal := by
  exact NLA.Proofs.RE06.svd_total 

theorem consume_query_bound (n m : ℕ) (hn : 0 < n) (ε : ℝ) (hε0 : 0 < ε) (hεh : ε < 1 / 2) :
    NLA.Computation.NonadaptiveMatrixQuery.QueryBound n m ε 4000000 0 := by
  exact NLA.Proofs.RE06.query_bound n m hn ε hε0 hεh

theorem consume_successful (n m : ℕ) (hn : 0 < n)
    (F : NLA.Computation.NonadaptiveMatrixQuery.Family n m) (hF : Function.Injective F)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε0 : 0 < ε) (hεh : ε < 1 / 2) :
    NLA.Computation.NonadaptiveMatrixQuery.Successful F A ε := by
  exact NLA.Proofs.RE06.successful n m hn F hF A ε hε0 hεh

theorem consume_original_claim  :
    NLA.Statements.RE06.OriginalClaim := by
  exact NLA.Proofs.RE06.original_claim 

theorem consume_explicit_claim  :
    NLA.Statements.RE06.ExplicitClaim := by
  exact NLA.Proofs.RE06.explicit_claim 

theorem consume_target  :
    NLA.Statements.RE06.Target := by
  exact NLA.Proofs.RE06.target 

theorem consume_reviewed_target : NLA.ReviewedStatements.RE06.Target := by
  rw [← live_reviewed_identity]
  exact NLA.Proofs.RE06.target

end NLA.Proofs.RE06.FullTargetAudit

#re06_theorem NLA.Proofs.RE06.svd_total
#assert_trust kernel NLA.Proofs.RE06.svd_total
#print axioms NLA.Proofs.RE06.svd_total

#re06_theorem NLA.Proofs.RE06.query_bound
#assert_trust kernel NLA.Proofs.RE06.query_bound
#print axioms NLA.Proofs.RE06.query_bound

#re06_theorem NLA.Proofs.RE06.successful
#assert_trust kernel NLA.Proofs.RE06.successful
#print axioms NLA.Proofs.RE06.successful

#re06_theorem NLA.Proofs.RE06.original_claim
#assert_trust kernel NLA.Proofs.RE06.original_claim
#print axioms NLA.Proofs.RE06.original_claim

#re06_theorem NLA.Proofs.RE06.explicit_claim
#assert_trust kernel NLA.Proofs.RE06.explicit_claim
#print axioms NLA.Proofs.RE06.explicit_claim

#re06_theorem NLA.Proofs.RE06.target
#assert_trust kernel NLA.Proofs.RE06.target
#print axioms NLA.Proofs.RE06.target

#re06_theorem NLA.Proofs.RE06.FullTargetAudit.live_reviewed_identity
#assert_trust kernel NLA.Proofs.RE06.FullTargetAudit.live_reviewed_identity
#print axioms NLA.Proofs.RE06.FullTargetAudit.live_reviewed_identity

#re06_theorem NLA.Proofs.RE06.FullTargetAudit.consume_svd_total
#assert_trust kernel NLA.Proofs.RE06.FullTargetAudit.consume_svd_total
#print axioms NLA.Proofs.RE06.FullTargetAudit.consume_svd_total

#re06_theorem NLA.Proofs.RE06.FullTargetAudit.consume_query_bound
#assert_trust kernel NLA.Proofs.RE06.FullTargetAudit.consume_query_bound
#print axioms NLA.Proofs.RE06.FullTargetAudit.consume_query_bound

#re06_theorem NLA.Proofs.RE06.FullTargetAudit.consume_successful
#assert_trust kernel NLA.Proofs.RE06.FullTargetAudit.consume_successful
#print axioms NLA.Proofs.RE06.FullTargetAudit.consume_successful

#re06_theorem NLA.Proofs.RE06.FullTargetAudit.consume_original_claim
#assert_trust kernel NLA.Proofs.RE06.FullTargetAudit.consume_original_claim
#print axioms NLA.Proofs.RE06.FullTargetAudit.consume_original_claim

#re06_theorem NLA.Proofs.RE06.FullTargetAudit.consume_explicit_claim
#assert_trust kernel NLA.Proofs.RE06.FullTargetAudit.consume_explicit_claim
#print axioms NLA.Proofs.RE06.FullTargetAudit.consume_explicit_claim

#re06_theorem NLA.Proofs.RE06.FullTargetAudit.consume_target
#assert_trust kernel NLA.Proofs.RE06.FullTargetAudit.consume_target
#print axioms NLA.Proofs.RE06.FullTargetAudit.consume_target

#re06_theorem NLA.Proofs.RE06.FullTargetAudit.consume_reviewed_target
#assert_trust kernel NLA.Proofs.RE06.FullTargetAudit.consume_reviewed_target
#print axioms NLA.Proofs.RE06.FullTargetAudit.consume_reviewed_target
