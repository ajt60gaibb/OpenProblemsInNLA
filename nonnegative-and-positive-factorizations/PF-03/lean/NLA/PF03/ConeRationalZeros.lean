import NLA.PF03.ConeQuadraticZeros
import NLA.PF03.RationalRay

/-! C13: an arbitrary rational vector in the full real quadratic zero set vanishes.
Sidney Holden: original mathematics. George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology: formalization;
Codex assistance. Author: /root. -/
set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

theorem cone_rational_zeros (x : Fin 7 → ℚ) (hx : castVector x ∈ K)
    (hq : quad quadraticSeed (castVector x) = 0) :
    x = 0 := by
  obtain ⟨i, t, _ht, heq⟩ := (cone_quadratic_zeros (castVector x) hx).2.mp hq
  apply rational_ray_zero (seedC i) _ x t heq
  exact ⟨0, 1, 0, 1, (seed_local_data i).2.2.2.2⟩

#print axioms cone_rational_zeros
#assert_trust kernel cone_rational_zeros
end NLA.PF03
