import Mathlib.Tactic
import LeanCert.Tactic.Verification
set_option leancert.trust "kernel"
theorem probe : True := by sorry
#print axioms probe
#assert_trust kernel probe
