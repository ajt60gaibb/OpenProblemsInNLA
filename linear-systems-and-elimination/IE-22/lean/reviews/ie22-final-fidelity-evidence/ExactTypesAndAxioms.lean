import NLA.IE22.Final

/- Independent exact full signature and axiom audit; generated from frozen Challenge bytes. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

/-- Genuine canonical supremum, not a default real sSup on an empty/unbounded set. -/
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (unitRowValues θ m n).Nonempty ∧ BddAbove (unitRowValues θ m n) ∧
    (∃ A : Mat m n, UnitRows A ∧ extremalValue θ m n = normalizedSingular θ A) ∧
    (∀ A : Mat m n, UnitRows A → normalizedSingular θ A ≤ extremalValue θ m n) ∧
    0 ≤ extremalValue θ m n ∧ extremalValue θ m n ≤ Real.sqrt n ∧
    ∀ A : Mat m n, 0 ≤ normalizedSingular θ A ∧
      normalizedSingular θ A ^ 2 = normalizedDeletion θ A := NLA.IE22.supremum_semantics
#print axioms NLA.IE22.supremum_semantics

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    0 ≤ sharpConstant θ ∧ sharpConstant θ ^ 2 = gaussianTrim θ ∧
    sharpConstant θ = Real.sqrt ((1 / Real.sqrt (2 * Real.pi)) *
      ∫ g in Icc (-gaussianCutoff θ) (gaussianCutoff θ), g ^ 2 * Real.exp (-(g ^ 2) / 2)) := NLA.IE22.constant_semantics
#print axioms NLA.IE22.constant_semantics

/-- Every subspace coordinate map is literal, with a correctly directed minimum inequality. -/
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (A : Mat m n)
    (J : Space d →ₗᵢ[ℝ] Space n) :
    (∀ g : Space d, matrixMap (projectedMatrix A J) g = matrixMap A (J g)) ∧
    (∀ i, ‖matrixRow (projectedMatrix A J) i‖ ≤ ‖matrixRow A i‖) ∧
    deletionSingular θ A ≤ deletionSingular θ (projectedMatrix A J) := NLA.IE22.projection_semantics
#print axioms NLA.IE22.projection_semantics

/-- Remove r leading covariance directions; all existence and spectral bounds are conclusions. -/
example (m n r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r ∧ r < n)
    (A : Mat m n) (hA : UnitRows A) :
    ∃ J : Space (n - r) →ₗᵢ[ℝ] Space n,
      operatorNorm (projectedMatrix A J) ^ 2 ≤ (m : ℝ) / ((r : ℝ) + 1) ∧
      (∀ i, ‖matrixRow (projectedMatrix A J) i‖ ≤ 1) ∧
      Matrix.trace (gramMatrix (projectedMatrix A J)) ≤ m := NLA.IE22.spectral_projection
#print axioms NLA.IE22.spectral_projection

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (B : Mat m d)
    (hB : ∀ i, ‖matrixRow B i‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (projectedObjective θ B t) (stdGaussian (Space d)) ∧
    (∫ g, projectedObjective θ B t g ∂stdGaussian (Space d)) ≤ gaussianTrim θ := NLA.IE22.gaussian_objective_mean
#print axioms NLA.IE22.gaussian_objective_mean

/-- Exact sharp Gaussian variance control is an obligation, never a final-target premise.
A full Gaussian Poincare theorem need not be selected if another exact proof suffices. -/
example (θ : ℝ) (m d : ℕ)
    (hm : 1 ≤ m) (hd : 1 ≤ d) (B : Mat m d) (t : ℝ) (ht : 0 ≤ t) :
    MemLp (projectedObjective θ B t) 2 (stdGaussian (Space d)) ∧
    Var[projectedObjective θ B t; stdGaussian (Space d)] ≤
      4 * t * operatorNorm B ^ 2 / m := NLA.IE22.gaussian_objective_variance
#print axioms NLA.IE22.gaussian_objective_variance

example (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (B : Mat m d) :
    MemLp (projectedEnergy B) 2 (stdGaussian (Space d)) ∧
    (∫ g, projectedEnergy B g ∂stdGaussian (Space d)) = Matrix.trace (gramMatrix B) / m ∧
    Var[projectedEnergy B; stdGaussian (Space d)] =
      2 * Matrix.trace (gramMatrix B * gramMatrix B) / (m : ℝ) ^ 2 := NLA.IE22.gaussian_energy_moments
#print axioms NLA.IE22.gaussian_energy_moments

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m : ℕ) (hm : 1 ≤ m) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hmean : (∑ i, y i) / (m : ℝ) ≤ 2) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ truncationScale θ ∧
      finiteTrim (retainedRows θ m) y / m = trimDual (retainedRows θ m) y t ∧
      ∀ u : ℝ, 0 ≤ u → trimDual (retainedRows θ m) y u ≤
        trimDual (retainedRows θ m) y t := NLA.IE22.bounded_trimming_threshold
#print axioms NLA.IE22.bounded_trimming_threshold

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m : ℕ) (hm : 1 ≤ m) (y : Fin m → ℝ) (s t : ℝ) :
    |trimDual (retainedRows θ m) y s - trimDual (retainedRows θ m) y t| ≤ |s - t| := NLA.IE22.threshold_lipschitz
#print axioms NLA.IE22.threshold_lipschitz

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : Finset ℝ, (∀ t ∈ C, t ∈ Icc 0 (truncationScale θ)) ∧
      (C.card : ℝ) ≤ truncationScale θ / δ + 2 ∧
      ∀ t ∈ Icc 0 (truncationScale θ), ∃ s ∈ C, |t - s| ≤ δ := NLA.IE22.threshold_grid
#print axioms NLA.IE22.threshold_grid

/-- All correlated projected rows are allowed; no independence is asserted. -/
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m d r : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hr : 1 ≤ r) (B : Mat m d)
    (hrows : ∀ i, ‖matrixRow B i‖ ≤ 1)
    (hop : operatorNorm B ^ 2 ≤ (m : ℝ) / ((r : ℝ) + 1))
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    MeasurableSet (ProjectionGood θ B δ) ∧
    (stdGaussian (Space d)).real (ProjectionGood θ B δ)ᶜ ≤ projectionFailure θ d r δ := NLA.IE22.projection_good_event_bound
#print axioms NLA.IE22.projection_good_event_bound

/-- The manuscript's exact boxed finite deterministic inequality, uniformly in m and A. -/
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r ∧ r < n)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (hfail : deterministicFailure θ n r δ < 1)
    (A : Mat m n) (hA : UnitRows A) :
    normalizedDeletion θ A ≤ deterministicBound θ n r δ := NLA.IE22.deterministic_finite_bound
#print axioms NLA.IE22.deterministic_finite_bound

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r ∧ r < n)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (hfail : deterministicFailure θ n r δ < 1) :
    extremalValue θ m n ^ 2 ≤ deterministicBound θ n r δ ∧
    extremalValue θ m n ≤ Real.sqrt (deterministicBound θ n r δ) := NLA.IE22.supremum_finite_bound
#print axioms NLA.IE22.supremum_finite_bound

/-- Exact source schedule, with bounds O_theta(n^(-1/6)) made explicit. -/
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    (∀ᶠ n in atTop, 1 ≤ deletionSchedule n ∧ deletionSchedule n < n ∧
      0 < errorSchedule n ∧ errorSchedule n < 1 ∧
      deterministicFailure θ n (deletionSchedule n) (errorSchedule n) < 1) ∧
    Tendsto errorSchedule atTop (𝓝 0) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      deterministicFailure θ n (deletionSchedule n) (errorSchedule n) ≤ C * errorSchedule n ∧
      deterministicBound θ n (deletionSchedule n) (errorSchedule n) - gaussianTrim θ ≤
        C * errorSchedule n := NLA.IE22.deterministic_schedule
#print axioms NLA.IE22.deterministic_schedule

/-- Explicit uniform squared error: C and N depend on theta alone, not on m or A. -/
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ m n : ℕ, 1 ≤ m → N ≤ n →
        (∀ A : Mat m n, UnitRows A →
          normalizedDeletion θ A ≤ gaussianTrim θ + C * errorSchedule n) ∧
        extremalValue θ m n ^ 2 ≤ gaussianTrim θ + C * errorSchedule n := NLA.IE22.universal_squared_rate
#print axioms NLA.IE22.universal_squared_rate

/-- Stronger source upper theorem: no aspect-ratio condition is required. -/
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ m n : ℕ, 1 ≤ m → N ≤ n →
      extremalValue θ m n ≤ sharpConstant θ + ε := NLA.IE22.uniform_upper_all_rows
#print axioms NLA.IE22.uniform_upper_all_rows

/-- Deterministic realization extracted from IE-21's exact positive-probability event. -/
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1)
    (hfail : finiteFailure m n t ε δ < 1) :
    ∃ A : Mat m n, UnitRows A ∧
      |normalizedDeletion θ A - gaussianTrim θ| ≤
        trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) := NLA.IE22.spherical_realization_from_finite_bound
#print axioms NLA.IE22.spherical_realization_from_finite_bound

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∃ A : Mat (m j) (n j), UnitRows A ∧
      sharpConstant θ - ε < normalizedSingular θ A := NLA.IE22.high_aspect_near_extremizers
#print axioms NLA.IE22.high_aspect_near_extremizers

/-- Every high-aspect sequence, not merely one diagonal construction. -/
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop) :
    Tendsto (fun j => extremalValue θ (m j) (n j)) atTop (𝓝 (sharpConstant θ)) := NLA.IE22.high_aspect_supremum_limit
#print axioms NLA.IE22.high_aspect_supremum_limit

/-- Literal original uniform property and its optimality. -/
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    EventualUniformUpper θ (sharpConstant θ) ∧
    ∀ C : ℝ, C < sharpConstant θ → ¬EventualUniformUpper θ C := NLA.IE22.canonical_sharp_constant
#print axioms NLA.IE22.canonical_sharp_constant

end NLA.IE22
