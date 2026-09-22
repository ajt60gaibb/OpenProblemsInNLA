import NLA.IE21.UniformTrimming
import NLA.IE21.FiniteSizeGeometry
import NLA.IE21.AsymptoticTail

/-! Complete quantitative IE-21 statements and full probability limits.
Original analytic argument: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace NLA.IE21

theorem finite_size_bound (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1) :
    (matrixLaw m n).real {A | ¬(0 < operatorNorm A ∧
      |normalizedOperator A - 1| ≤ t ∧
      |normalizedDeletion θ A - gaussianTrim θ| ≤
        trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) ∧
      |deletionRatio θ A - gaussianTrim θ| ≤ finiteRatioError θ m n t ε δ)} ≤
      finiteFailure m n t ε δ := by
  let : IsProbabilityMeasure (matrixLaw m n) := (product_row_semantics m n (by omega)).1
  have hsub : {A : Mat m n | ¬(0 < operatorNorm A ∧
      |normalizedOperator A - 1| ≤ t ∧
      |normalizedDeletion θ A - gaussianTrim θ| ≤
        trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) ∧
      |deletionRatio θ A - gaussianTrim θ| ≤ finiteRatioError θ m n t ε δ)} ⊆
      (GoodEvent θ m n t ε δ)ᶜ := by
    intro A hbad hgood
    exact hbad (goodEvent_statistics θ hθ m n hm (by omega) A t ε δ ht.2 hgood)
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (uniform_trim_concentration θ hθ m n hm hn t ε δ ht hε hδ)

lemma product_ratio_tail_bound (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1) :
    (matrixLaw m n).real {A | |deletionRatio θ A - gaussianTrim θ| >
      finiteRatioError θ m n t ε δ} ≤ finiteFailure m n t ε δ := by
  let : IsProbabilityMeasure (matrixLaw m n) := (product_row_semantics m n (by omega)).1
  apply (measureReal_mono (s₂ := {A : Mat m n | ¬(0 < operatorNorm A ∧
      |normalizedOperator A - 1| ≤ t ∧
      |normalizedDeletion θ A - gaussianTrim θ| ≤
        trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) ∧
      |deletionRatio θ A - gaussianTrim θ| ≤ finiteRatioError θ m n t ε δ)})
    (fun A hA hgood => (not_lt_of_ge hgood.2.2.2) hA) (measure_ne_top _ _)).trans
  exact finite_size_bound θ hθ m n hm hn t ε δ ht hε hδ

theorem finite_size_independent_rows {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) (A : Ω → Mat m n)
    (hA : IndependentSphereRows μ A)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1) :
    μ.real {ω | |deletionRatio θ (A ω) - gaussianTrim θ| >
      finiteRatioError θ m n t ε δ} ≤ finiteFailure m n t ε δ := by
  rw [random_row_tail_eq μ θ hθ (by omega) A hA]
  exact product_ratio_tail_bound θ hθ m n hm hn t ε δ ht hε hδ

theorem spherical_ratio_limit (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop)
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun j => (matrixLaw (m j) (n j)).real
      {A | |deletionRatio θ A - gaussianTrim θ| > η}) atTop (𝓝 0) :=
  spherical_ratio_limit_of_finite_bounds θ hθ m n hm hn hnlim hQlim
    (fun j hnj t ε δ ht hε hδ => product_ratio_tail_bound θ hθ (m j) (n j)
      (hm j) hnj t ε δ ht hε hδ) η hη

theorem original_random_row_limit (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop)
    (Ω : ℕ → Type*) [∀ j, MeasurableSpace (Ω j)]
    (μ : (j : ℕ) → Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (A : (j : ℕ) → Ω j → Mat (m j) (n j))
    (hA : ∀ j, IndependentSphereRows (μ j) (A j)) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun j => (μ j).real
      {ω | |deletionRatio θ (A j ω) - gaussianTrim θ| > η}) atTop (𝓝 0) := by
  have heq : (fun j => (μ j).real {ω | |deletionRatio θ (A j ω) - gaussianTrim θ| > η}) =
      (fun j => (matrixLaw (m j) (n j)).real {B | |deletionRatio θ B - gaussianTrim θ| > η}) :=
    funext (fun j => random_row_tail_eq (μ j) θ hθ (hn j) (A j) (hA j) η)
  rw [heq]
  exact spherical_ratio_limit θ hθ m n hm hn hnlim hQlim η hη

end NLA.IE21
