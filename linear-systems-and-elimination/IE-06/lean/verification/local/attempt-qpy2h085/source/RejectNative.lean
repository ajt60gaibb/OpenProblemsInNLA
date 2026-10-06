import Mathlib.Tactic
import LeanCert.Tactic.Verification
theorem rejectNative : (1 : Nat) = 1 := by native_decide
#assert_trust kernel rejectNative
