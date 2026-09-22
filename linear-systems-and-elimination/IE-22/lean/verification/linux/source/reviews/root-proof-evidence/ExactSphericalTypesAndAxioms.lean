import NLA.IE22.SphericalRealization
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
open NLA.IE21 NLA.IE22

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1)
    (hfail : finiteFailure m n t ε δ < 1) :
    ∃ A : Mat m n, UnitRows A ∧
      |normalizedDeletion θ A - gaussianTrim θ| ≤
        trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) := by
  exact NLA.IE22.spherical_realization_from_finite_bound θ hθ m n hm hn t ε δ ht hε hδ hfail
#print axioms NLA.IE22.spherical_realization_from_finite_bound

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∃ A : Mat (m j) (n j), UnitRows A ∧
      sharpConstant θ - ε < normalizedSingular θ A := by
  exact NLA.IE22.high_aspect_near_extremizers θ hθ m n hm hn hnlim hQlim ε hε
#print axioms NLA.IE22.high_aspect_near_extremizers

