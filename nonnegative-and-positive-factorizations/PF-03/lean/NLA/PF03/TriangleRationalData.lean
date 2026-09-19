import NLA.PF03.CubicLowerBounds

/-!
Literal rational triangle and generator identities and the three rational
barycentric lower bounds. No proposed generator is accepted as an assumption.
Original mathematics and seed: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
namespace NLA.PF03

theorem triangle_literal : triangle = RawData.triangle := by
  ext r j
  fin_cases r <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem generator_literal : generatorMatrix = RawData.generators := by
  ext r j
  fin_cases r <;> fin_cases j <;> decide +kernel

theorem barycentric_lower_positive (j : Fin 3) :
    0 < cubicLower (RawData.barycentricCoefficients j) := by
  fin_cases j <;> decide +kernel

#print axioms generator_literal
#assert_trust kernel generator_literal
#print axioms barycentric_lower_positive
#assert_trust kernel barycentric_lower_positive

end NLA.PF03
