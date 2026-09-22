import NLA.IE22.AsymptoticConclusion
import NLA.IE22.DeterministicBound

/-!
Complete canonical sharp constant and all quantitative/asymptotic consequences.
Original mathematical proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

theorem universal_squared_rate (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ m n : ℕ, 1 ≤ m → N ≤ n →
        (∀ A : Mat m n, UnitRows A →
          normalizedDeletion θ A ≤ gaussianTrim θ + C * errorSchedule n) ∧
        extremalValue θ m n ^ 2 ≤ gaussianTrim θ + C * errorSchedule n := by
  exact universal_squared_rate_of_finite_bound θ hθ
    (fun m n r hm hr δ hδ hf A hA => deterministic_finite_bound θ hθ m n r hm hr δ hδ hf A hA)

theorem uniform_upper_all_rows (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ m n : ℕ, 1 ≤ m → N ≤ n →
      extremalValue θ m n ≤ sharpConstant θ + ε := by
  exact uniform_upper_all_rows_of_rate θ hθ (universal_squared_rate θ hθ) ε hε

theorem high_aspect_supremum_limit (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop) :
    Tendsto (fun j => extremalValue θ (m j) (n j)) atTop (𝓝 (sharpConstant θ)) := by
  exact high_aspect_supremum_limit_of_uniform_upper θ hθ
    (uniform_upper_all_rows θ hθ) m n hm hn hnlim hQlim

theorem canonical_sharp_constant (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    EventualUniformUpper θ (sharpConstant θ) ∧
    ∀ C : ℝ, C < sharpConstant θ → ¬EventualUniformUpper θ C := by
  refine ⟨?_, no_smaller_uniform_constant θ hθ⟩
  intro ε hε
  obtain ⟨N, _, hN⟩ := uniform_upper_all_rows θ hθ ε hε
  refine ⟨N, 0, ?_⟩
  intro m n hm _ hn _
  exact hN m n hm hn

end NLA.IE22
