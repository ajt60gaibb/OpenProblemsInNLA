import LeanCert.Tactic.LeanCert

/-! Infrastructure control only: this proves no catalog target. The exact
rational bound exercises the requested LeanCert kernel certificate route. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Statements.KernelSmoke

theorem log_two_upper : Real.log 2 < (7 / 10 : ℝ) := by
  leancert (trust := kernel)

#assert_trust kernel log_two_upper
#print axioms log_two_upper

end NLA.Statements.KernelSmoke
