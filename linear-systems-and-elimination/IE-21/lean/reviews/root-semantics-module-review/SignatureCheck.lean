import NLA.IE21.FiniteTrimming
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE21

example {m n : ℕ} (A : Mat m n) (hn : 1 ≤ n) :
    (∀ (x : Space n) (i : Fin m), matrixMap A x i = ∑ j, A i j * x j) ∧
    (∃ x : Space n, ‖x‖ = 1 ∧ ‖matrixMap A x‖ = operatorNorm A) ∧
    (∀ x : Space n, ‖matrixMap A x‖ ≤ operatorNorm A * ‖x‖) ∧
    (∀ (S : Finset (Fin m)) (x : Space n),
      retainedNorm A S x ^ 2 = ∑ i ∈ S, (matrixMap A x i) ^ 2) := by
  exact matrix_semantics A hn

example {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (hn : 1 ≤ n) :
    0 ≤ deletionSingular θ A ∧
    (∃ (S : Finset (Fin m)) (x : Space n),
      S.card = retainedRows θ m ∧ ‖x‖ = 1 ∧
      deletionSingular θ A = retainedNorm A S x) ∧
    (∀ (S : Finset (Fin m)) (x : Space n),
      S.card = retainedRows θ m → ‖x‖ = 1 →
      deletionSingular θ A ≤ retainedNorm A S x) := by
  exact deletion_minimum θ hθ A hn

example {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (hn : 1 ≤ n) :
    (retainedRows θ m = 0 → deletionSingular θ A = 0) ∧
    ((∃ S : Finset (Fin m), S.card = retainedRows θ m ∧
      ∃ x : Space n, x ≠ 0 ∧ Matrix.toEuclideanLin (retainedMatrix A S) x = 0) →
      deletionSingular θ A = 0) := by
  exact deletion_zero_cases θ hθ A hn

example {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m)
    (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) :
    (∃ S : Finset (Fin m), S.card = k ∧ finiteTrim k y = ∑ i ∈ S, y i) ∧
    (∀ S : Finset (Fin m), S.card = k → finiteTrim k y ≤ ∑ i ∈ S, y i) ∧
    (∃ t : ℝ, 0 ≤ t ∧ finiteTrim k y / m = trimDual k y t ∧
      ∀ u : ℝ, 0 ≤ u → trimDual k y u ≤ trimDual k y t) := by
  exact finite_trimming_semantics hm k hk y hy

example {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∃ x : Space n, ‖x‖ = 1 ∧ directionalTrim θ A x = normalizedDeletion θ A) ∧
    (∀ x : Space n, ‖x‖ = 1 → normalizedDeletion θ A ≤ directionalTrim θ A x) := by
  exact directional_minimum θ hθ A hm hn

example (m n : ℕ) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (hn : 1 ≤ n) :
    Measurable (deletionSingular (m := m) (n := n) θ) ∧
    Measurable (operatorNorm (m := m) (n := n)) ∧
    Measurable (deletionRatio (m := m) (n := n) θ) ∧
    ∀ t ε δ, MeasurableSet (GoodEvent θ m n t ε δ) := by
  exact statistics_measurable m n θ hθ hn

end NLA.IE21
