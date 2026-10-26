import NLA.Proofs.RE06.SVDTotal
import NLA.Proofs.RE06.QueryBound
import NLA.Statements.RE06

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
#assert_trust kernel NLA.Proofs.RE06.svd_total
#assert_trust kernel NLA.Proofs.RE06.query_bound
#assert_trust kernel NLA.Proofs.RE06.CountAudit.exact_svd_total
#assert_trust kernel NLA.Proofs.RE06.CountAudit.exact_query_bound
#assert_trust kernel NLA.Proofs.RE06.CountAudit.live_frozen_identity
#print axioms NLA.Proofs.RE06.svd_total
#print axioms NLA.Proofs.RE06.query_bound
