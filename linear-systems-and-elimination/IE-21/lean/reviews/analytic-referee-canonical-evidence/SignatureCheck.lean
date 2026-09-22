import NLA.IE21.GaussianTrimming
import NLA.IE21.PopulationTrimming
import NLA.IE21.SphericalLaw
import NLA.IE21.RowLaw
import NLA.IE21.GaussianPolar
import NLA.IE21.AspectSchedule
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE21

example (n : ℕ) (hn : 1 ≤ n) :
    0 < surfaceMeasure n Set.univ ∧ surfaceMeasure n Set.univ < ⊤ ∧
    IsProbabilityMeasure (surfaceLaw n) ∧ IsProbabilityMeasure (sphereLaw n) ∧
    (sphereLaw n) {u | ‖u‖ = 1} = 1 := by
  exact surface_probability n hn

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    0 < gaussianCutoff θ ∧
    (gaussianReal 0 1).real {g | |g| ≤ gaussianCutoff θ} = θ ∧
    (∀ a : ℝ, 0 < a → (gaussianReal 0 1).real {g | |g| ≤ a} = θ →
      a = gaussianCutoff θ) ∧
    gaussianTrim θ = ∫ g in {g | |g| ≤ gaussianCutoff θ}, g ^ 2 ∂gaussianReal 0 1 ∧
    0 ≤ gaussianTrim θ ∧ gaussianTrim θ ≤ 1 := by
  exact gaussian_constant θ hθ

example (m n : ℕ) (hn : 1 ≤ n) :
    IsProbabilityMeasure (matrixLaw m n) ∧
    IndependentSphereRows (matrixLaw m n) (fun A => A) ∧
    (matrixLaw m n) {A | ∀ i, ‖matrixRow A i‖ = 1} = 1 := by
  exact product_row_semantics m n hn

example {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n : ℕ} (A : Ω → Mat m n)
    (hA : IndependentSphereRows μ A) : μ.map A = matrixLaw m n := by
  exact independent_row_transport μ A hA

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop) :
    (∀ᶠ j in atTop, 2 ≤ n j ∧ 0 < aspectParameter (m j) (n j) ∧
      aspectParameter (m j) (n j) < 1 ∧
      aspectParameter (m j) (n j) ≤ (1 - θ) / 2) ∧
    Tendsto (fun j => finiteFailure (m j) (n j)
      (aspectParameter (m j) (n j)) (aspectParameter (m j) (n j))
      (aspectParameter (m j) (n j))) atTop (𝓝 0) ∧
    Tendsto (fun j => finiteRatioError θ (m j) (n j)
      (aspectParameter (m j) (n j)) (aspectParameter (m j) (n j))
      (aspectParameter (m j) (n j))) atTop (𝓝 0) := by
  exact aspect_schedule θ hθ m n hm hn hnlim hQlim

example (n : ℕ) (hn : 1 ≤ n) :
    (stdGaussian (Space n)).map gaussianDirection = sphereLaw n ∧
    (stdGaussian (Space n)) {0} = 0 ∧
    IndepFun (fun g : Space n => ‖g‖) gaussianDirection (stdGaussian (Space n)) := by
  exact ⟨gaussian_direction_law n hn, gaussian_zero_mass n hn,
    gaussian_radius_direction_independent n hn⟩

end NLA.IE21
