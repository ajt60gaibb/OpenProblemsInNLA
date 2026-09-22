import NLA.IE22.SphericalRealization
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
open NLA.IE21 NLA.IE22

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (unitRowValues θ m n).Nonempty ∧ BddAbove (unitRowValues θ m n) ∧
    (∃ A : Mat m n, UnitRows A ∧ extremalValue θ m n = normalizedSingular θ A) ∧
    (∀ A : Mat m n, UnitRows A → normalizedSingular θ A ≤ extremalValue θ m n) ∧
    0 ≤ extremalValue θ m n ∧ extremalValue θ m n ≤ Real.sqrt n ∧
    ∀ A : Mat m n, 0 ≤ normalizedSingular θ A ∧
      normalizedSingular θ A ^ 2 = normalizedDeletion θ A :=
  NLA.IE22.supremum_semantics θ hθ m n hm hn

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    0 ≤ sharpConstant θ ∧ sharpConstant θ ^ 2 = gaussianTrim θ ∧
    sharpConstant θ = Real.sqrt ((1 / Real.sqrt (2 * Real.pi)) *
      ∫ g in Icc (-gaussianCutoff θ) (gaussianCutoff θ), g ^ 2 * Real.exp (-(g ^ 2) / 2)) :=
  NLA.IE22.constant_semantics θ hθ

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1)
    (hfail : finiteFailure m n t ε δ < 1) :
    ∃ A : Mat m n, UnitRows A ∧
      |normalizedDeletion θ A - gaussianTrim θ| ≤
        trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) :=
  NLA.IE22.spherical_realization_from_finite_bound θ hθ m n hm hn t ε δ ht hε hδ hfail

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∃ A : Mat (m j) (n j), UnitRows A ∧
      sharpConstant θ - ε < normalizedSingular θ A :=
  NLA.IE22.high_aspect_near_extremizers θ hθ m n hm hn hnlim hQlim ε hε

#print axioms NLA.IE22.continuous_normalizedSingular

#print axioms NLA.IE22.isCompact_unitRows

#print axioms NLA.IE22.unitRows_nonempty

#print axioms NLA.IE22.unitRowValues_eq_image

#print axioms NLA.IE22.normalizedSingular_nonneg_sq

#print axioms NLA.IE22.normalizedSingular_le_sqrt_dim

#print axioms NLA.IE22.supremum_semantics

#print axioms NLA.IE22.constant_semantics

#print axioms NLA.IE22.spherical_realization_from_finite_bound

#print axioms NLA.IE22.trimming_error_le_ratio_error

#print axioms NLA.IE22.high_aspect_near_extremizers
