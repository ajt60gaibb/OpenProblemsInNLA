import Mathlib.Tactic
import LeanCert.Tactic.Verification
set_option leancert.trust "kernel"
theorem probe : (List.range 37).reverse.length = 37 := by native_decide
#print axioms probe
#assert_trust kernel probe
