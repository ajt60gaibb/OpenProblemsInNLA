import NLA.IE21.CovarianceConcentration
import NLA.IE21.SphericalMGF

/-! Complete frozen covariance concentration theorem for IE-21.
Original analytic argument: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NLA.IE21

theorem covariance_concentration (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t : ℝ) (ht : 0 < t ∧ t ≤ 1) :
    (matrixLaw m n).real {A | covarianceError A > t} ≤
      2 * (9 : ℝ) ^ n * Real.exp (-(m : ℝ) * t ^ 2 / 512) :=
  covariance_concentration_of_mgf m n hm hn
    (fun x hx a ha => spherical_quadratic_mgf n hn x hx a ha) t ht

end NLA.IE21
