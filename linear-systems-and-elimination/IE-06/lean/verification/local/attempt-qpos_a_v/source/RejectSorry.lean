import Mathlib.Tactic
import LeanCert.Tactic.Verification
theorem rejectSorry : True := by sorry
#assert_trust kernel rejectSorry
