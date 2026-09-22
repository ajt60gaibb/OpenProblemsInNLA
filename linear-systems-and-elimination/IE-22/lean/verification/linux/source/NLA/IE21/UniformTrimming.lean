import NLA.IE21.UniformTrimmingBound
import NLA.IE21.Covariance
import NLA.IE21.SphericalTrimming
import NLA.IE21.PointwiseTrimming

/-!
The complete frozen uniform trimming bound for IE-21, with all probability and
surface-to-Gaussian inputs supplied by their proved implementation modules.
Original proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NLA.IE21

theorem uniform_trim_concentration (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1) :
    (matrixLaw m n).real (GoodEvent θ m n t ε δ)ᶜ ≤ finiteFailure m n t ε δ := by
  have hn1 : 1 ≤ n := by omega
  let : IsProbabilityMeasure (matrixLaw m n) := (product_row_semantics m n hn1).1
  have h := uniform_trim_probability_of_bounds θ hθ m n hn1 (matrixLaw m n)
    t ε δ ht.1.le hδ.1
    (2 * (9 : ℝ) ^ n * Real.exp (-(m : ℝ) * t ^ 2 / 512))
    (5 * Real.exp (-2 * (m : ℝ) * ε ^ 2)) (by positivity)
    (covariance_concentration m n hm hn t ⟨ht.1, ht.2.le⟩)
    (fun x hx => spherical_gaussian_trimming θ hθ n hn x hx)
    (fun x hx => pointwise_trim_concentration θ hθ m n hm hn x hx ε hε)
  convert h using 1
  unfold finiteFailure
  ring

end NLA.IE21
