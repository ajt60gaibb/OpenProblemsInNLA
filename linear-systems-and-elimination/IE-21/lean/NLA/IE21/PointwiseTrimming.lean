import NLA.IE21.TrimmingConcentration
import NLA.IE21.PointwiseTrimmingSemantics
import NLA.IE21.RowLaw
import NLA.IE21.SphericalMoments

/-! Exact frozen pointwise IE-21 trimming concentration statement. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NLA.IE21

/-- The exact finite-sample estimate for independent normalized surface rows. -/
theorem pointwise_trim_concentration (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) (x : Space n) (hx : ‖x‖ = 1)
    (ε : ℝ) (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) :
    (matrixLaw m n).real {A |
      |directionalTrim θ A x - populationTrim θ (sphereLaw n) (directionalEnergy x)| >
        2 * truncationScale θ * ε + truncationScale θ / m} ≤
      5 * Real.exp (-2 * (m : ℝ) * ε ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  let : IsProbabilityMeasure (sphereLaw n) := (surface_probability n hn1).2.2.2.1
  have hrows := product_row_semantics m n hn1
  let : IsProbabilityMeasure (matrixLaw m n) := hrows.1
  have h := independent_trim_concentration (sphereLaw n) (matrixLaw m n) hm
    (fun i A => matrixRow A i) (measurable_matrixRow m n) hrows.2.1.2.1 hrows.2.1.2.2
    (directionalEnergy x) (by unfold directionalEnergy; fun_prop)
    (directionalEnergy_integrable n hn1 x hx)
    (by intro u; unfold directionalEnergy; positivity)
    (directionalEnergy_mean n hn1 x hx) θ hθ ε hε
  simpa only [← directionalTrim_eq_energy_trim θ hθ] using h

end NLA.IE21
