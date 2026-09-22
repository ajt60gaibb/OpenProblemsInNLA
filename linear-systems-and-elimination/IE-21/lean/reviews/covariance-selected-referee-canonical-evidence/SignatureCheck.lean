import NLA.IE21.SphericalMGF
import NLA.IE21.Covariance

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NLA.IE21

example (n : ℕ) (hn : 2 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (a : ℝ) (ha : |a| ≤ 1 / 8) :
    Integrable (fun u => Real.exp (a * (directionalEnergy x u - 1))) (sphereLaw n) ∧
    (∫ u, Real.exp (a * (directionalEnergy x u - 1)) ∂sphereLaw n) ≤
      Real.exp (32 * a ^ 2) := by
  exact spherical_quadratic_mgf n hn x hx a ha

example (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t : ℝ) (ht : 0 < t ∧ t ≤ 1) :
    (matrixLaw m n).real {A | covarianceError A > t} ≤
      2 * (9 : ℝ) ^ n * Real.exp (-(m : ℝ) * t ^ 2 / 512) := by
  exact covariance_concentration m n hm hn t ht

end NLA.IE21
