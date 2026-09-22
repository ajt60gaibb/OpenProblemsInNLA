import NLA.IE22.TrimmingThreshold
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
open NLA.IE21 NLA.IE22

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m : ℕ) (hm : 1 ≤ m) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hmean : (∑ i, y i) / (m : ℝ) ≤ 2) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ truncationScale θ ∧
      finiteTrim (retainedRows θ m) y / m = trimDual (retainedRows θ m) y t ∧
      ∀ u : ℝ, 0 ≤ u → trimDual (retainedRows θ m) y u ≤
        trimDual (retainedRows θ m) y t := by
  exact NLA.IE22.bounded_trimming_threshold θ hθ m hm y hy hmean
#print axioms NLA.IE22.bounded_trimming_threshold

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m : ℕ) (hm : 1 ≤ m) (y : Fin m → ℝ) (s t : ℝ) :
    |trimDual (retainedRows θ m) y s - trimDual (retainedRows θ m) y t| ≤ |s - t| := by
  exact NLA.IE22.threshold_lipschitz θ hθ m hm y s t
#print axioms NLA.IE22.threshold_lipschitz

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : Finset ℝ, (∀ t ∈ C, t ∈ Icc 0 (truncationScale θ)) ∧
      (C.card : ℝ) ≤ truncationScale θ / δ + 2 ∧
      ∀ t ∈ Icc 0 (truncationScale θ), ∃ s ∈ C, |t - s| ≤ δ := by
  exact NLA.IE22.threshold_grid θ hθ δ hδ
#print axioms NLA.IE22.threshold_grid
