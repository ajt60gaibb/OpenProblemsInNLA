import NLA.Statements.TR26
import Reviewed.TR26
set_option leancert.trust "kernel"
/-! Frozen statement identity, not a proof of the full Target. -/
example : NLA.Statements.TR26.Target = NLA.ReviewedStatements.TR26.Target := rfl
