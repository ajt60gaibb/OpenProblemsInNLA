import LeanCert.Tactic.LeanCert
import LeanCert.Tactic.Verification

/-! An infrastructure control only. This scalar estimate is not an IE-06 target.
The explicit per-call trust setting supplements the file-wide kernel default. -/
set_option leancert.trust "kernel"

namespace NLA.IE06.Infrastructure

theorem kernelModeControl : Real.log 2 < (7 : ℝ) / 10 := by
  leancert (trust := kernel)

#assert_trust kernel kernelModeControl
#print axioms kernelModeControl

end NLA.IE06.Infrastructure
