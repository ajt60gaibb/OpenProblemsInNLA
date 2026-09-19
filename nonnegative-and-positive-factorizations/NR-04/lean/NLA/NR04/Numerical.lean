/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

Original mathematical proof: Matthew J. Colbrook, University of Cambridge,
The nonnegative rank of the nine-point linear distance matrix, Section 5.
This is only the consumed fixed-constant boundary of its ordinary-rank proof.
No interval over matrix entries, factor entries or dimensions is used.
-/
import NLA.NR04.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NR04

/-- C01: the determinant's exact positive value, certified in kernel mode. -/
theorem minor_eight_positive : 0 < (8 : ℝ) := by
  interval_decide (trust := kernel)

#print axioms minor_eight_positive
#assert_trust kernel minor_eight_positive

end NLA.NR04
