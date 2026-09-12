/- Exact all-count roots of unity for Colbrook's MI-03 construction.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
AI-assisted; Apache 2.0. -/
import NLA.MI03.Modulus

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI03

theorem root_of_unity_data_proved (k : ℕ) (hk : 2 ≤ k) :
    ‖rootOfUnity k‖ = 1 ∧
    (∑ j : Fin k, rootOfUnity k ^ (j : ℕ)) = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hr : IsPrimitiveRoot (rootOfUnity k) k := Complex.isPrimitiveRoot_exp k hk0
  refine ⟨hr.norm'_eq_one hk0, ?_⟩
  rw [Fin.sum_univ_eq_sum_range]
  exact hr.geom_sum_eq_zero (by omega)

theorem root_power_star (k : ℕ) (hk : 2 ≤ k) (j : ℕ) :
    rootOfUnity k ^ j * star (rootOfUnity k ^ j) = 1 := by
  rw [Complex.star_def, Complex.mul_conj]
  rw [← Complex.sq_norm, norm_pow, (root_of_unity_data_proved k hk).1]
  norm_num

theorem sqrt_three_sq : (((Real.sqrt 3 : ℝ) : ℂ)) ^ (2 : ℕ) = 3 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)

end NLA.MI03
