import NLA.IE22.SupremumSemantics
import NLA.IE22.TrimmingThreshold
import NLA.IE22.GaussianMean
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
      normalizedSingular θ A ^ 2 = normalizedDeletion θ A := by
  exact NLA.IE22.supremum_semantics θ hθ m n hm hn
#print axioms NLA.IE22.supremum_semantics

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    0 ≤ sharpConstant θ ∧ sharpConstant θ ^ 2 = gaussianTrim θ ∧
    sharpConstant θ = Real.sqrt ((1 / Real.sqrt (2 * Real.pi)) *
      ∫ g in Icc (-gaussianCutoff θ) (gaussianCutoff θ), g ^ 2 * Real.exp (-(g ^ 2) / 2)) := by
  exact NLA.IE22.constant_semantics θ hθ
#print axioms NLA.IE22.constant_semantics

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

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (B : Mat m d)
    (hB : ∀ i, ‖matrixRow B i‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (projectedObjective θ B t) (stdGaussian (Space d)) ∧
    (∫ g, projectedObjective θ B t g ∂stdGaussian (Space d)) ≤ gaussianTrim θ := by
  exact NLA.IE22.gaussian_objective_mean θ hθ m d hm hd B hB t ht
#print axioms NLA.IE22.gaussian_objective_mean

