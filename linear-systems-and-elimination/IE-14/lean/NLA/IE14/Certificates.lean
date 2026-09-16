/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import LeanCert.Tactic

set_option leancert.trust "kernel"
namespace NLA.IE14

/-- Both components are consumed by the exact half entries of the all-size witness. -/
theorem half_bounds_certificate : (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) ≤ 1 := by
  constructor
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)

#assert_trust kernel half_bounds_certificate
#print axioms half_bounds_certificate

end NLA.IE14
