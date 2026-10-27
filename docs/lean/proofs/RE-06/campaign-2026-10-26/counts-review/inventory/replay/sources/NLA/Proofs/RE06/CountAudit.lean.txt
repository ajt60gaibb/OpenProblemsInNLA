import NLA.Proofs.RE06.SVDTotal
import NLA.Proofs.RE06.QueryBound
import NLA.Statements.RE06
import Reviewed.RE06

set_option autoImplicit false
set_option leancert.trust "kernel"

open Lean Elab Command in
elab "#actual_theorem " n:ident : command => do
  let d ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? d with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected actual theorem declaration"

namespace NLA.Proofs.RE06.CountAudit

theorem exact_svd_total : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal :=
  NLA.Proofs.RE06.svd_total

theorem exact_query_bound (n m : ℕ) (hn : 0 < n) (ε : ℝ)
    (hε0 : 0 < ε) (hεh : ε < 1 / 2) :
    NLA.Computation.NonadaptiveMatrixQuery.QueryBound n m ε 4000000 0 :=
  NLA.Proofs.RE06.query_bound n m hn ε hε0 hεh

theorem live_frozen_identity : NLA.Statements.RE06.Target =
    NLA.ReviewedStatements.RE06.Target := rfl

end NLA.Proofs.RE06.CountAudit

#actual_theorem NLA.Proofs.RE06.svd_total
#actual_theorem NLA.Proofs.RE06.query_bound
#actual_theorem NLA.Proofs.RE06.Counts.queryList_length
#actual_theorem NLA.Proofs.RE06.Counts.makePlan_query_count
#actual_theorem NLA.Proofs.RE06.Counts.logWidth_pos
#actual_theorem NLA.Proofs.RE06.Counts.rootWidth_pos
#actual_theorem NLA.Proofs.RE06.Counts.logWidth_le_root_sq
#actual_theorem NLA.Proofs.RE06.Counts.rootWidth_le_sqrt_add_one
#actual_theorem NLA.Proofs.RE06.Counts.log_size_ge_one
#actual_theorem NLA.Proofs.RE06.Counts.logWidth_le_two_log_add_one
#actual_theorem NLA.Proofs.RE06.Counts.rootWidth_le_three_sqrt_log
#actual_theorem NLA.Proofs.RE06.Counts.scaled_self_le_div
#actual_theorem NLA.Proofs.RE06.Counts.step_ceil_bound
#actual_theorem NLA.Proofs.RE06.Counts.firstWidth_bound
#actual_theorem NLA.Proofs.RE06.Counts.total_width_bound
#assert_trust kernel NLA.Proofs.RE06.svd_total
#assert_trust kernel NLA.Proofs.RE06.query_bound
#assert_trust kernel NLA.Proofs.RE06.Counts.queryList_length
#assert_trust kernel NLA.Proofs.RE06.Counts.makePlan_query_count
#assert_trust kernel NLA.Proofs.RE06.Counts.logWidth_pos
#assert_trust kernel NLA.Proofs.RE06.Counts.rootWidth_pos
#assert_trust kernel NLA.Proofs.RE06.Counts.logWidth_le_root_sq
#assert_trust kernel NLA.Proofs.RE06.Counts.rootWidth_le_sqrt_add_one
#assert_trust kernel NLA.Proofs.RE06.Counts.log_size_ge_one
#assert_trust kernel NLA.Proofs.RE06.Counts.logWidth_le_two_log_add_one
#assert_trust kernel NLA.Proofs.RE06.Counts.rootWidth_le_three_sqrt_log
#assert_trust kernel NLA.Proofs.RE06.Counts.scaled_self_le_div
#assert_trust kernel NLA.Proofs.RE06.Counts.step_ceil_bound
#assert_trust kernel NLA.Proofs.RE06.Counts.firstWidth_bound
#assert_trust kernel NLA.Proofs.RE06.Counts.total_width_bound
#assert_trust kernel NLA.Proofs.RE06.CountAudit.exact_svd_total
#assert_trust kernel NLA.Proofs.RE06.CountAudit.exact_query_bound
#assert_trust kernel NLA.Proofs.RE06.CountAudit.live_frozen_identity
#print axioms NLA.Proofs.RE06.svd_total
#print axioms NLA.Proofs.RE06.query_bound
