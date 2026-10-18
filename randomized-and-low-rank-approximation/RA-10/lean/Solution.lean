import Identity
import NLA.Proofs.RA10.OperatorMonotoneRepresentation
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

/- The pinned proof supplies C = 11 for the unchanged full target. -/
theorem NLA.RA10.target : NLA.ReviewedStatements.RA10.Target := by
  rw [← NLA.RA10.statement_identity]
  exact NLA.Proofs.RA10.ra10_target

#assert_trust kernel NLA.RA10.target
#print axioms NLA.RA10.target
