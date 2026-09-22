import NLA.IE22.AsymptoticConclusion
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
open NLA.IE21 NLA.IE22

-- Explicit assumption audits; these are helper implications, not exports of selected final targets.
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (hfinite : ∀ (m n r : ℕ), 1 ≤ m → (1 ≤ r ∧ r < n) →
      ∀ δ : ℝ, (0 < δ ∧ δ < 1) → deterministicFailure θ n r δ < 1 →
      ∀ A : Mat m n, UnitRows A → normalizedDeletion θ A ≤ deterministicBound θ n r δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ m n : ℕ, 1 ≤ m → N ≤ n →
        (∀ A : Mat m n, UnitRows A →
          normalizedDeletion θ A ≤ gaussianTrim θ + C * errorSchedule n) ∧
        extremalValue θ m n ^ 2 ≤ gaussianTrim θ + C * errorSchedule n :=
  universal_squared_rate_of_finite_bound θ hθ hfinite

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (hrate : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ m n : ℕ, 1 ≤ m → N ≤ n →
        (∀ A : Mat m n, UnitRows A → normalizedDeletion θ A ≤ gaussianTrim θ + C * errorSchedule n) ∧
        extremalValue θ m n ^ 2 ≤ gaussianTrim θ + C * errorSchedule n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ m n : ℕ, 1 ≤ m → N ≤ n →
      extremalValue θ m n ≤ sharpConstant θ + ε :=
  uniform_upper_all_rows_of_rate θ hθ hrate ε hε

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
      ∀ m n : ℕ, 1 ≤ m → N ≤ n → extremalValue θ m n ≤ sharpConstant θ + ε)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop) :
    Tendsto (fun j => extremalValue θ (m j) (n j)) atTop (𝓝 (sharpConstant θ)) :=
  high_aspect_supremum_limit_of_uniform_upper θ hθ hupper m n hm hn hnlim hQlim

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (C : ℝ) (hC : C < sharpConstant θ) :
    ¬EventualUniformUpper θ C := no_smaller_uniform_constant θ hθ C hC

#print axioms NLA.IE22.universal_squared_rate_of_finite_bound

#print axioms NLA.IE22.uniform_upper_all_rows_of_rate

#print axioms NLA.IE22.high_aspect_supremum_limit_of_uniform_upper

#print axioms NLA.IE22.no_smaller_uniform_constant
