/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Kernel audit of the exact FR-12 proof. Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
AI-assisted formalization. This counting/algebraic argument needs no interval
certificate; LeanCert is used for its explicit kernel trust audit.
-/
import NLA.FR12.Growth
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.FR12

#assert_trust kernel counting_semantics_proved
#print axioms counting_semantics_proved
#assert_trust kernel injective_doubling_proved
#print axioms injective_doubling_proved
#assert_trust kernel factorial_doubling_proved
#print axioms factorial_doubling_proved
#assert_trust kernel power_two_nonempty_proved
#print axioms power_two_nonempty_proved
#assert_trust kernel power_two_lower_bound_proved
#print axioms power_two_lower_bound_proved
#assert_trust kernel counterexample_proved
#print axioms counterexample_proved
#assert_trust kernel not_countingConjecture_proved
#print axioms not_countingConjecture_proved

end NLA.FR12
