import LeanCert.Tactic.LeanCert
import LeanCert.Tactic.Verification
set_option leancert.trust "kernel"
theorem numericProbe : Real.log 2 < (7 : ℝ) / 10 := by
  leancert (trust := kernel)
#assert_trust kernel numericProbe
#print axioms numericProbe
