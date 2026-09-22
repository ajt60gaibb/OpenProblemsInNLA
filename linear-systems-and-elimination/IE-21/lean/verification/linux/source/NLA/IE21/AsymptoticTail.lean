import NLA.IE21.AspectSchedule
import NLA.IE21.RowLaw
import NLA.IE21.FiniteTrimming

/-! Probability-limit assembly for the full IE-21 aspect schedule.
Original analytic argument: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace NLA.IE21

lemma spherical_ratio_limit_of_finite_bounds (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop)
    (hfinite : ∀ j, 2 ≤ n j → ∀ t ε δ : ℝ, (0 < t ∧ t < 1) →
      (0 < ε ∧ ε ≤ (1 - θ) / 2) → (0 < δ ∧ δ < 1) →
      (matrixLaw (m j) (n j)).real
        {A | |deletionRatio θ A - gaussianTrim θ| > finiteRatioError θ (m j) (n j) t ε δ} ≤
          finiteFailure (m j) (n j) t ε δ)
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun j => (matrixLaw (m j) (n j)).real
      {A | |deletionRatio θ A - gaussianTrim θ| > η}) atTop (𝓝 0) := by
  obtain ⟨hadm, hfail, herr⟩ := aspect_schedule θ hθ m n hm hn hnlim hQlim
  apply squeeze_zero' (Eventually.of_forall (fun j => measureReal_nonneg)) _ hfail
  filter_upwards [hadm, herr.eventually (gt_mem_nhds hη)] with j hj he
  let d := aspectParameter (m j) (n j)
  let : IsProbabilityMeasure (matrixLaw (m j) (n j)) :=
    (product_row_semantics (m j) (n j) (hn j)).1
  have hsub : {A : Mat (m j) (n j) | |deletionRatio θ A - gaussianTrim θ| > η} ⊆
      {A | |deletionRatio θ A - gaussianTrim θ| > finiteRatioError θ (m j) (n j) d d d} := by
    intro A hA
    exact lt_trans he hA
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (hfinite j hj.1 d d d ⟨hj.2.1, hj.2.2.1⟩ ⟨hj.2.1, hj.2.2.2⟩ ⟨hj.2.1, hj.2.2.1⟩)

lemma random_row_tail_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    {m n : ℕ} (hn : 1 ≤ n) (A : Ω → Mat m n) (hA : IndependentSphereRows μ A)
    (η : ℝ) :
    μ.real {ω | |deletionRatio θ (A ω) - gaussianTrim θ| > η} =
      (matrixLaw m n).real {B | |deletionRatio θ B - gaussianTrim θ| > η} := by
  rw [← independent_row_transport μ A hA]
  have hs : MeasurableSet {B : Mat m n | |deletionRatio θ B - gaussianTrim θ| > η} :=
    measurableSet_lt measurable_const (((statistics_measurable m n θ hθ hn).2.2.1.sub_const _).abs)
  exact (map_measureReal_apply hA.1 hs).symm

end NLA.IE21
