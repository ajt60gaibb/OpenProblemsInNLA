import NLA.IE22.DeterministicBound
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory NLA.IE21 NLA.IE22
open scoped ENNReal BigOperators RealInnerProductSpace
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r ∧ r < n)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (hfail : deterministicFailure θ n r δ < 1)
    (A : Mat m n) (hA : UnitRows A) :
    normalizedDeletion θ A ≤ deterministicBound θ n r δ := NLA.IE22.deterministic_finite_bound θ hθ m n r hm hr δ hδ hfail A hA

example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r ∧ r < n)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (hfail : deterministicFailure θ n r δ < 1) :
    extremalValue θ m n ^ 2 ≤ deterministicBound θ n r δ ∧
    extremalValue θ m n ≤ Real.sqrt (deterministicBound θ n r δ) := NLA.IE22.supremum_finite_bound θ hθ m n r hm hr δ hδ hfail

#print axioms NLA.IE22.deletionSingular_sq_le_finiteTrim
#print axioms NLA.IE22.deletionSingular_sq_le_of_projectionGood
#print axioms NLA.IE22.projectionGood_nonempty_of_probability_bound
#print axioms NLA.IE22.supremum_bound_of_all_matrices
#print axioms NLA.IE22.normalizedDeletion_le_of_projectionGood
#print axioms NLA.IE22.deterministic_bound_of_projected_probability
#print axioms NLA.IE22.deterministic_finite_bound
#print axioms NLA.IE22.supremum_finite_bound
