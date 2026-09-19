import NLA.PF03.SeedLocalAlgebra

/-!
Exact C06 rational certificates for cone4: six restriction entries, all three
kernel rows, both strict lower bounds, and the specified nonzero minor.
Original mathematics and seed: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
namespace NLA.PF03

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem seed_local_rational_certificate4 : SeedLocalRationalCertificate 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab k
    fin_cases a <;> fin_cases b <;> fin_cases k
    all_goals first | omega | decide +kernel
  · intro r k
    fin_cases r <;> fin_cases k <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms seed_local_rational_certificate4
#assert_trust kernel seed_local_rational_certificate4

end NLA.PF03
