import Mathlib.Tactic
import LeanCert.Tactic.Verification
set_option leancert.trust "kernel"
theorem probe : (2 : ℚ) / 3 + 1 / 3 = 1 := by norm_num
#assert_trust kernel probe
#print axioms probe
