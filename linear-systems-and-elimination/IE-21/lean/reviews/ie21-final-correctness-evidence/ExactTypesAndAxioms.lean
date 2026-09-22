import NLA.IE21.FiniteSize
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE21
-- Exact frozen type: surface_probability
example : ∀ (n : ℕ) (hn : 1 ≤ n), 0 < surfaceMeasure n Set.univ ∧ surfaceMeasure n Set.univ < ⊤ ∧
    IsProbabilityMeasure (surfaceLaw n) ∧ IsProbabilityMeasure (sphereLaw n) ∧
    (sphereLaw n) {u | ‖u‖ = 1} = 1 := @NLA.IE21.surface_probability
#print axioms NLA.IE21.surface_probability
-- Exact frozen type: gaussian_surface_correspondence
example : ∀ (n : ℕ) (hn : 1 ≤ n), (stdGaussian (Space n)).map gaussianDirection = sphereLaw n ∧
    (stdGaussian (Space n)) {0} = 0 ∧
    IndepFun (fun g : Space n => ‖g‖) gaussianDirection (stdGaussian (Space n)) ∧
    (∫ g : Space n, ‖g‖ ^ 2 ∂stdGaussian (Space n)) = n ∧
    (∫ g : Space n, (‖g‖ ^ 2 - n) ^ 2 ∂stdGaussian (Space n)) = 2 * n := @NLA.IE21.gaussian_surface_correspondence
#print axioms NLA.IE21.gaussian_surface_correspondence
-- Exact frozen type: product_row_semantics
example : ∀ (m n : ℕ) (hn : 1 ≤ n), IsProbabilityMeasure (matrixLaw m n) ∧
    IndependentSphereRows (matrixLaw m n) (fun A => A) ∧
    (matrixLaw m n) {A | ∀ i, ‖matrixRow A i‖ = 1} = 1 := @NLA.IE21.product_row_semantics
#print axioms NLA.IE21.product_row_semantics
-- Exact frozen type: independent_row_transport
example : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n : ℕ} (A : Ω → Mat m n)
    (hA : IndependentSphereRows μ A), μ.map A = matrixLaw m n := @NLA.IE21.independent_row_transport
#print axioms NLA.IE21.independent_row_transport
-- Exact frozen type: matrix_semantics
example : ∀ {m n : ℕ} (A : Mat m n) (hn : 1 ≤ n), (∀ (x : Space n) (i : Fin m), matrixMap A x i = ∑ j, A i j * x j) ∧
    (∃ x : Space n, ‖x‖ = 1 ∧ ‖matrixMap A x‖ = operatorNorm A) ∧
    (∀ x : Space n, ‖matrixMap A x‖ ≤ operatorNorm A * ‖x‖) ∧
    (∀ (S : Finset (Fin m)) (x : Space n),
      retainedNorm A S x ^ 2 = ∑ i ∈ S, (matrixMap A x i) ^ 2) := @NLA.IE21.matrix_semantics
#print axioms NLA.IE21.matrix_semantics
-- Exact frozen type: deletion_minimum
example : ∀ {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (hn : 1 ≤ n), 0 ≤ deletionSingular θ A ∧
    (∃ (S : Finset (Fin m)) (x : Space n),
      S.card = retainedRows θ m ∧ ‖x‖ = 1 ∧
      deletionSingular θ A = retainedNorm A S x) ∧
    (∀ (S : Finset (Fin m)) (x : Space n),
      S.card = retainedRows θ m → ‖x‖ = 1 →
      deletionSingular θ A ≤ retainedNorm A S x) := @NLA.IE21.deletion_minimum
#print axioms NLA.IE21.deletion_minimum
-- Exact frozen type: deletion_zero_cases
example : ∀ {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (hn : 1 ≤ n), (retainedRows θ m = 0 → deletionSingular θ A = 0) ∧
    ((∃ S : Finset (Fin m), S.card = retainedRows θ m ∧
      ∃ x : Space n, x ≠ 0 ∧ Matrix.toEuclideanLin (retainedMatrix A S) x = 0) →
      deletionSingular θ A = 0) := @NLA.IE21.deletion_zero_cases
#print axioms NLA.IE21.deletion_zero_cases
-- Exact frozen type: finite_trimming_semantics
example : ∀ {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m)
    (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i), (∃ S : Finset (Fin m), S.card = k ∧ finiteTrim k y = ∑ i ∈ S, y i) ∧
    (∀ S : Finset (Fin m), S.card = k → finiteTrim k y ≤ ∑ i ∈ S, y i) ∧
    (∃ t : ℝ, 0 ≤ t ∧ finiteTrim k y / m = trimDual k y t ∧
      ∀ u : ℝ, 0 ≤ u → trimDual k y u ≤ trimDual k y t) := @NLA.IE21.finite_trimming_semantics
#print axioms NLA.IE21.finite_trimming_semantics
-- Exact frozen type: directional_minimum
example : ∀ {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (hm : 1 ≤ m) (hn : 1 ≤ n), (∃ x : Space n, ‖x‖ = 1 ∧ directionalTrim θ A x = normalizedDeletion θ A) ∧
    (∀ x : Space n, ‖x‖ = 1 → normalizedDeletion θ A ≤ directionalTrim θ A x) := @NLA.IE21.directional_minimum
#print axioms NLA.IE21.directional_minimum
-- Exact frozen type: statistics_measurable
example : ∀ (m n : ℕ) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (hn : 1 ≤ n), Measurable (deletionSingular (m := m) (n := n) θ) ∧
    Measurable (operatorNorm (m := m) (n := n)) ∧
    Measurable (deletionRatio (m := m) (n := n) θ) ∧
    ∀ t ε δ, MeasurableSet (GoodEvent θ m n t ε δ) := @NLA.IE21.statistics_measurable
#print axioms NLA.IE21.statistics_measurable
-- Exact frozen type: gaussian_constant
example : ∀ (θ : ℝ) (hθ : 0 < θ ∧ θ < 1), 0 < gaussianCutoff θ ∧
    (gaussianReal 0 1).real {g | |g| ≤ gaussianCutoff θ} = θ ∧
    (∀ a : ℝ, 0 < a → (gaussianReal 0 1).real {g | |g| ≤ a} = θ →
      a = gaussianCutoff θ) ∧
    gaussianTrim θ = ∫ g in {g | |g| ≤ gaussianCutoff θ}, g ^ 2 ∂gaussianReal 0 1 ∧
    0 ≤ gaussianTrim θ ∧ gaussianTrim θ ≤ 1 := @NLA.IE21.gaussian_constant
#print axioms NLA.IE21.gaussian_constant
-- Exact frozen type: spherical_moments
example : ∀ (n : ℕ) (hn : 2 ≤ n) (x : Space n) (hx : ‖x‖ = 1)
    (r : ℕ), Integrable (fun u => directionalEnergy x u ^ r) (sphereLaw n) ∧
    (∫ u, directionalEnergy x u ^ r ∂sphereLaw n) =
      ((n : ℝ) ^ r * ∏ j ∈ Finset.range r, (2 * (j : ℝ) + 1)) /
        (∏ j ∈ Finset.range r, ((n : ℝ) + 2 * j)) ∧
    (∫ u, directionalEnergy x u ^ r ∂sphereLaw n) ≤
      2 ^ r * (Nat.factorial r : ℝ) := @NLA.IE21.spherical_moments
#print axioms NLA.IE21.spherical_moments
-- Exact frozen type: spherical_quadratic_mgf
example : ∀ (n : ℕ) (hn : 2 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (a : ℝ) (ha : |a| ≤ 1 / 8), Integrable (fun u => Real.exp (a * (directionalEnergy x u - 1))) (sphereLaw n) ∧
    (∫ u, Real.exp (a * (directionalEnergy x u - 1)) ∂sphereLaw n) ≤
      Real.exp (32 * a ^ 2) := @NLA.IE21.spherical_quadratic_mgf
#print axioms NLA.IE21.spherical_quadratic_mgf
-- Exact frozen type: spherical_gaussian_trimming
example : ∀ (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (n : ℕ) (hn : 2 ≤ n) (x : Space n) (hx : ‖x‖ = 1), |populationTrim θ (sphereLaw n) (directionalEnergy x) - gaussianTrim θ| ≤
      Real.sqrt (2 / (n : ℝ)) := @NLA.IE21.spherical_gaussian_trimming
#print axioms NLA.IE21.spherical_gaussian_trimming
-- Exact frozen type: pointwise_trim_concentration
example : ∀ (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) (x : Space n) (hx : ‖x‖ = 1)
    (ε : ℝ) (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2), (matrixLaw m n).real {A |
      |directionalTrim θ A x - populationTrim θ (sphereLaw n) (directionalEnergy x)| >
        2 * truncationScale θ * ε + truncationScale θ / m} ≤
      5 * Real.exp (-2 * (m : ℝ) * ε ^ 2) := @NLA.IE21.pointwise_trim_concentration
#print axioms NLA.IE21.pointwise_trim_concentration
-- Exact frozen type: sphere_net
example : ∀ (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ), ∃ C : Finset (Space n), (∀ x ∈ C, ‖x‖ = 1) ∧
      (C.card : ℝ) ≤ (1 + 2 / δ) ^ n ∧
      ∀ x : Space n, ‖x‖ = 1 → ∃ y ∈ C, ‖x - y‖ ≤ δ := @NLA.IE21.sphere_net
#print axioms NLA.IE21.sphere_net
-- Exact frozen type: covariance_concentration
example : ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t : ℝ) (ht : 0 < t ∧ t ≤ 1), (matrixLaw m n).real {A | covarianceError A > t} ≤
      2 * (9 : ℝ) ^ n * Real.exp (-(m : ℝ) * t ^ 2 / 512) := @NLA.IE21.covariance_concentration
#print axioms NLA.IE21.covariance_concentration
-- Exact frozen type: uniform_trim_concentration
example : ∀ (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1), (matrixLaw m n).real (GoodEvent θ m n t ε δ)ᶜ ≤ finiteFailure m n t ε δ := @NLA.IE21.uniform_trim_concentration
#print axioms NLA.IE21.uniform_trim_concentration
-- Exact frozen type: finite_size_bound
example : ∀ (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1), (matrixLaw m n).real {A | ¬(0 < operatorNorm A ∧
      |normalizedOperator A - 1| ≤ t ∧
      |normalizedDeletion θ A - gaussianTrim θ| ≤
        trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) ∧
      |deletionRatio θ A - gaussianTrim θ| ≤ finiteRatioError θ m n t ε δ)} ≤
      finiteFailure m n t ε δ := @NLA.IE21.finite_size_bound
#print axioms NLA.IE21.finite_size_bound
-- Exact frozen type: finite_size_independent_rows
example : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) (A : Ω → Mat m n)
    (hA : IndependentSphereRows μ A)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1), μ.real {ω | |deletionRatio θ (A ω) - gaussianTrim θ| >
      finiteRatioError θ m n t ε δ} ≤ finiteFailure m n t ε δ := @NLA.IE21.finite_size_independent_rows
#print axioms NLA.IE21.finite_size_independent_rows
-- Exact frozen type: aspect_schedule
example : ∀ (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop), (∀ᶠ j in atTop, 2 ≤ n j ∧ 0 < aspectParameter (m j) (n j) ∧
      aspectParameter (m j) (n j) < 1 ∧
      aspectParameter (m j) (n j) ≤ (1 - θ) / 2) ∧
    Tendsto (fun j => finiteFailure (m j) (n j)
      (aspectParameter (m j) (n j)) (aspectParameter (m j) (n j))
      (aspectParameter (m j) (n j))) atTop (𝓝 0) ∧
    Tendsto (fun j => finiteRatioError θ (m j) (n j)
      (aspectParameter (m j) (n j)) (aspectParameter (m j) (n j))
      (aspectParameter (m j) (n j))) atTop (𝓝 0) := @NLA.IE21.aspect_schedule
#print axioms NLA.IE21.aspect_schedule
-- Exact frozen type: spherical_ratio_limit
example : ∀ (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop)
    (η : ℝ) (hη : 0 < η), Tendsto (fun j => (matrixLaw (m j) (n j)).real
      {A | |deletionRatio θ A - gaussianTrim θ| > η}) atTop (𝓝 0) := @NLA.IE21.spherical_ratio_limit
#print axioms NLA.IE21.spherical_ratio_limit
-- Exact frozen type: original_random_row_limit
example : ∀ (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop)
    (Ω : ℕ → Type*) [∀ j, MeasurableSpace (Ω j)]
    (μ : (j : ℕ) → Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (A : (j : ℕ) → Ω j → Mat (m j) (n j))
    (hA : ∀ j, IndependentSphereRows (μ j) (A j)) (η : ℝ) (hη : 0 < η), Tendsto (fun j => (μ j).real
      {ω | |deletionRatio θ (A j ω) - gaussianTrim θ| > η}) atTop (𝓝 0) := @NLA.IE21.original_random_row_limit
#print axioms NLA.IE21.original_random_row_limit
end NLA.IE21
